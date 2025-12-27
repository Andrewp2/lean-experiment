import{r as o,u as z,j as n,S as j,c as R}from"./index-CmsUpJRH.js";const B=`theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Nat.add_succ, ih]
`,K=`lemma mul_comm (a b : Nat) : a * b = b * a := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    simp [Nat.mul_succ, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
`,I=`lemma bool_or (p q : Bool) : p || q = true := by
  cases p <;> cases q <;> decide
`,D=`/-
A line in the plane is called sunny if it is not parallel to any of the $x$-axis, the $y$-axis, and the line $x+y=0$.
Let $n \\geqslant 3$ be a given integer. Determine all nonnegative integers $k$ such that there exist $n$ distinct lines in the plane satisfying both of the following:
- for all positive integers $a$ and $b$ with $a+b \\leqslant n+1$, the point $(a, b)$ is on at least one of the lines; and
- exactly $k$ of the $n$ lines are sunny.

Answer: 0, 1, 3
-/

import HarmonicLean.Imports

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace IMO2025P1

/-
A line in the plane is called sunny if it is not parallel to the $x$-axis, the $y$-axis, or the line $x+y=0$. A line is non-sunny otherwise.
--/
def Sunny (l : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c, l = { v | a * v.1 + b * v.2 + c = 0 } ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b

def NonSunny (l : Set (ℝ × ℝ)) : Prop :=
  (∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ l = { v | a * v.1 + b * v.2 + c = 0 }) ∧ ¬ Sunny l

/-
For a positive integer $n$, define the set of points $S_n = \\{(a,b) \\in \\mathbb{Z}^+ \\times \\mathbb{Z}^+ : a+b \\leq n+1\\}$.
--/
def s (n : ℕ) : Set (ℝ × ℝ) :=
  { v | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 ∧ v = ((a : ℝ), (b : ℝ)) }

/-
A line is non-sunny if and only if its equation can be written in the form $x=c$, $y=c$, or $x+y=c$ for some constant $c$.
-
-/
lemma lem_non_sunny_form (l : Set (ℝ × ℝ))
  (h_is_line : ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ l = { v | a * v.1 + b * v.2 + c = 0 }) :
  NonSunny l ↔ (∃ c : ℝ, l = { v | v.1 = c }) ∨
                 (∃ c : ℝ, l = { v | v.2 = c }) ∨
                 (∃ c : ℝ, l = { v | v.1 + v.2 = c }) := by
                   bound;
                   · have := a;
                     -- By definition of non-sunny, if a line is non-sunny, then it is not sunny, which means it is parallel to one of the axes or the line x+y=0.
                     have h_parallel : ¬Sunny {v : ℝ × ℝ | w * v.1 + w_1 * v.2 + w_2 = 0} → (w = 0 ∨ w_1 = 0 ∨ w = w_1) := by
                       -- By definition of sunny, if a line is not sunny, then it must be parallel to one of the axes or the line x+y=0.
                       intro h_not_sunny
                       by_contra h_contra;
                       exact h_not_sunny ⟨ w, w_1, w_2, rfl, by tauto ⟩;
                     rcases h_parallel this.2 with ( rfl | rfl | rfl );
                     · exact Or.inr <| Or.inl ⟨ -w_2 / w_1, by ext; simp ( config := { decide := Bool.true } ) [ field_simps, show w_1 ≠ 0 by aesop ] ; constructor <;> intros <;> linarith ⟩;
                     · exact Or.inl ⟨ -w_2 / w, by ext; simp ( config := { decide := Bool.true } ) [ field_simps, show w ≠ 0 by aesop ] ; constructor <;> intros <;> linarith ⟩;
                     · exact Or.inr <| Or.inr <| ⟨ -w_2 / w, by ext; simp ( config := { decide := Bool.true } ) [ field_simps, show w ≠ 0 by aesop ] ; constructor <;> intros <;> linarith ⟩;
                   · -- If the line is of the form $x = c$, then it is parallel to the $y$-axis and thus not sunny.
                     have h_not_sunny : ¬Sunny {v : ℝ × ℝ | v.1 = w_3} := by
                       rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
                       norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
                       exact h₃ ( by linarith [ h₁.1 w_3 0 rfl, h₁.1 w_3 1 rfl ] );
                     -- Since the line $x = w_3$ is not sunny, we can conclude that it is non-sunny.
                     apply And.intro;
                     · exact ⟨ w, w_1, w_2, left, rfl ⟩;
                     · -- Since the line $x = w_3$ is not sunny, we can conclude that it is non-sunny by definition.
                       rw [h]
                       exact h_not_sunny;
                   · constructor;
                     · exact ⟨ w, w_1, w_2, left, rfl ⟩;
                     · rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
                       -- Since the line is of the form $y = c$, it is parallel to the $x$-axis and thus not sunny.
                       have h_parallel_x : ∀ v : ℝ × ℝ, v ∈ {v | w * v.1 + w_1 * v.2 + w_2 = 0} ↔ v.2 = w_3 := by
                         exact?;
                       norm_num [ h₁ ] at h_parallel_x;
                       have := h_parallel_x 0 w_3; have := h_parallel_x 1 w_3; norm_num at * ; cases lt_or_gt_of_ne h₂ <;> cases lt_or_gt_of_ne h₃ <;> nlinarith;
                   · constructor;
                     · exact ⟨ w, w_1, w_2, left, rfl ⟩;
                     · rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
                       norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at *;
                       exact h₄ ( by linarith [ h₁.1 _ _ ( h.2 ( w_3 - 1 ) 1 ( by ring ) ), h₁.1 _ _ ( h.2 w_3 0 ( by ring ) ) ] )

/-
For $n \\ge 3$, let $\\mathcal{L}_0 = \\{x=i : i \\in \\{1, 2, \\dots, n\\}\\}$. The set $\\mathcal{L}_0$ consists of $n$ distinct non-sunny lines.
-
-/
lemma lem_k0_construction (n : ℕ) (hn : n ≥ 3) :
  let L0 := Finset.image (fun i : ℕ => {v : ℝ × ℝ | v.1 = (i : ℝ)}) (Finset.Icc 1 n);
  L0.card = n ∧ ∀ l ∈ L0, NonSunny l := by
    aesop;
    · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using Set.ext_iff.mp hxy ( x, 0 ) ] ; aesop;
    · constructor;
      · exact ⟨ 1, 0, -x, by norm_num, by ext; aesop ; linarith ⟩;
      · -- The line $x = x$ is parallel to the y-axis, so it is not sunny by definition.
        unfold Sunny
        simp;
        intro a b c h₁ h₂ h₃; rw [ Set.ext_iff ] at h₁; have h₄ := h₁ ( x, 0 ) ; have h₅ := h₁ ( x, 1 ) ; norm_num at h₄ h₅ ; cases lt_or_gt_of_ne h₂ <;> cases lt_or_gt_of_ne h₃ <;> nlinarith;

/-
For any integer $n \\ge 3$, $k=0$ is a possible value.
-
-/
lemma lem_k0_possible (n : ℕ) (hn : n ≥ 3) :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 0 := by
      -- Apply the lemma to obtain the set of lines.
      obtain ⟨lines, hlines⟩ := lem_k0_construction n hn;
      use Finset.image ( fun i : ℕ => { v : ℝ × ℝ | v.1 = ( i : ℝ ) } ) ( Finset.Icc 1 n );
      aesop;
      · exact ⟨ 1, 0, by norm_num, -x, by ext; aesop ; linarith ⟩;
      · cases a_1 ; aesop;
        linarith;
      · -- Since all lines in the image are non-sunny, the filter of sunny lines is empty.
        ext l
        simp [hlines];
        exact fun x hx₁ hx₂ hx₃ => fun h => hlines l x hx₁ hx₂ hx₃ |>.2 h

/-
For $n \\ge 3$, let $\\mathcal{L}_1 = \\{y=x\\} \\cup \\{x+y=j : j \\in \\{3, 4, \\dots, n+1\\}\\}$. The set $\\mathcal{L}_1$ consists of $n$ distinct lines, of which exactly one is sunny.
-
-/
lemma lem_k1_construction (n : ℕ) (hn : n ≥ 3) :
  let L1 := insert {v : ℝ × ℝ | v.2 = v.1}
    (Finset.image (fun j : ℕ => {v : ℝ × ℝ | v.1 + v.2 = (j : ℝ)}) (Finset.Icc 3 (n+1)));
  L1.card = n ∧ (L1.filter Sunny).card = 1 := by
    field_simp;
    rw [ Finset.card_insert_of_not_mem, Finset.filter_insert ];
    · rw [ Finset.card_image_of_injective ];
      · rw [ Finset.filter_eq_empty_iff.mpr ] <;> aesop;
        · -- Since $n \\geq 3$, we have $n - 1 + 1 = n$.
          rw [Nat.sub_add_cancel (by linarith)];
        · -- The line $y = x$ is sunny because it is not parallel to the $x$-axis, $y$-axis, or the line $x + y = 0$.
          have h_sunny : Sunny {v : ℝ × ℝ | v.2 = v.1} := by
            use 1, -1, 0;
            exact ⟨ by ext; aesop ; linarith, by norm_num, by norm_num, by norm_num ⟩;
          contradiction;
        · obtain ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ := a;
          norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
          exact h₄ ( by linarith [ h₁.1 ( w - 1 ) 1 ( by ring ), h₁.1 w 0 ( by ring ) ] );
      · exact fun a b h => by simpa using Set.ext_iff.mp h ( 0, ↑a ) ;
    · -- The line $y = x$ is not of the form $x + y = j$ for any $j$, so it cannot be in the image of the function.
      simp [Set.ext_iff];
      exact fun x hx₁ hx₂ => ⟨ 0, x, by norm_num; linarith [ ( by norm_cast : ( 3 : ℝ ) ≤ x ) ] ⟩

/-
For any integer $n \\ge 3$, $k=1$ is a possible value.
-
-/
lemma lem_k1_possible (n : ℕ) (hn : n ≥ 3) :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 1 := by
      -- Let's construct the set of lines L1 as described.
      set L1 : Finset (Set (ℝ × ℝ)) := insert {v : ℝ × ℝ | v.2 = v.1} (Finset.image (fun j : ℕ => {v : ℝ × ℝ | v.1 + v.2 = (j : ℝ)}) (Finset.Icc 3 (n + 1)));
      refine' ⟨ L1, _, _, _, _ ⟩;
      · aesop;
        · exact ⟨ -1, 1, by norm_num, 0, by ext; aesop ; linarith ⟩;
        · exact ⟨ 1, 1, by norm_num, -w, by ext; aesop ; linarith ⟩;
      · rw [ Finset.card_insert_of_not_mem ] <;> norm_num;
        · -- The function j ↦ {v | v.1 + v.2 = j} is injective, so the cardinality of the image is the same as the cardinality of the domain.
          have h_inj : Function.Injective (fun j : ℕ => {v : ℝ × ℝ | v.1 + v.2 = (j : ℝ)}) := by
            exact fun a b h => by simpa using Set.ext_iff.mp h ( 0, ↑a ) ;
          rw [ Finset.card_image_of_injective _ h_inj ] ; norm_num;
          omega;
        · intro x hx₁ hx₂; rw [ Set.ext_iff ] ; push_neg; use ( 0, x ) ; aesop;
      · -- For any point $p \\in s n$, if $p.1 = p.2$, then $p$ lies on the line $y = x$. Otherwise, since $p.1 + p.2 \\leq n + 1$, there exists $j \\in \\{3, 4, \\ldots, n + 1\\}$ such that $p.1 + p.2 = j$, so $p$ lies on the line $x + y = j$.
        intro p hp
        by_cases h_eq : p.1 = p.2;
        · aesop;
        · cases hp ; aesop;
          exact Or.inr ⟨ w + w_1, ⟨ by omega, by omega ⟩, by norm_cast ⟩;
      · have := lem_k1_construction n hn;
        exact this.2

/-
For $n=3$, there exists a set of 3 distinct lines covering $S_3$ with $k=3$ sunny lines.
-
-/
lemma lem_n3_k3_exists :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = 3 ∧
    (∀ p ∈ s 3, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 3 := by
      -- Let's choose the lines $L_1: y=x$, $L_2: y=-2x+5$, and $L_3: y=-x/2+5/2$.
      use { {v : ℝ × ℝ | v.2 = v.1}, {v : ℝ × ℝ | v.2 = -2 * v.1 + 5}, {v : ℝ × ℝ | v.2 = -v.1 / 2 + 5 / 2} };
      refine' ⟨ _, _, _, _ ⟩;
      · norm_num;
        -- For each line, we can find coefficients $a$, $b$, and $c$ such that the line equation holds and $a$ and $b$ are not both zero.
        exact ⟨⟨-1, 1, by norm_num, 0, by ext; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> linarith⟩, ⟨2, 1, by norm_num, -5, by ext; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> linarith⟩, ⟨1, 2, by norm_num, -5, by ext; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> linarith⟩⟩;
      · rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton ] <;> norm_num [ Set.ext_iff ];
        · -- Let's choose any $x \\neq \\frac{5}{3}$.
          use 0; norm_num;
        · exact ⟨ ⟨ 0, by norm_num ⟩, ⟨ 0, by norm_num ⟩ ⟩;
      · unfold s; aesop;
        rcases w with ( _ | _ | _ | _ | w ) <;> rcases w_1 with ( _ | _ | _ | _ | w_1 ) <;> norm_num at * <;> linarith;
      · -- Since all three lines are sunny, the filter of sunny lines in the set should include all three elements. Therefore, the cardinality of the filter is 3.
        have h_sunny : ∀ l ∈ ({ {v : ℝ × ℝ | v.2 = v.1}, {v : ℝ × ℝ | v.2 = -2 * v.1 + 5}, {v : ℝ × ℝ | v.2 = -v.1 / 2 + 5 / 2} } : Finset (Set (ℝ × ℝ))), Sunny l := by
          aesop;
          · use 1, -1, 0;
            -- To prove the equality of sets, we show each set is a subset of the other.
            simp [Set.ext_iff];
            exact ⟨ fun a b => ⟨ fun h => by linarith, fun h => by linarith ⟩, by norm_num ⟩;
          · use 2, 1, -5;
            exact ⟨ Set.ext fun x => by aesop ; linarith, by norm_num, by norm_num, by norm_num ⟩;
          · exact ⟨ 1 / 2, 1, -5 / 2, by ext; norm_num; constructor <;> intros <;> linarith, by norm_num, by norm_num, by norm_num ⟩;
        rw [ Finset.filter_true_of_mem h_sunny ];
        rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton ] <;> norm_num [ Set.ext_iff ];
        · exact ⟨ 0, by norm_num ⟩;
        · exact ⟨ ⟨ 0, by norm_num ⟩, ⟨ 0, by norm_num ⟩ ⟩

/-
Let $\\mathcal{L}_m$ be a set of $m$ lines covering $S_m$. Let $\\mathcal{L}_{m+1} = \\mathcal{L}_m \\cup \\{x+y=m+2\\}$. Then $\\mathcal{L}_{m+1}$ covers $S_{m+1}$.
-
-/
lemma lem_induction_step_coverage (m : ℕ)
  (Lm : Finset (Set (ℝ × ℝ)))
  (h_cover : ∀ p ∈ s m, ∃ l ∈ Lm, p ∈ l) :
  let L_new := {v : ℝ × ℝ | v.1 + v.2 = (m : ℝ) + 2};
  let Lm1 := Lm ∪ {L_new};
  ∀ p ∈ s (m+1), ∃ l ∈ Lm1, p ∈ l := by
    aesop;
    cases a ; aesop;
    by_cases h : w + w_1 ≤ m + 1;
    · exact Exists.elim ( h_cover w w_1 ⟨ w, w_1, left, left_1, by linarith, rfl ⟩ ) fun l hl => ⟨ l, Or.inl hl.1, hl.2 ⟩;
    · -- Since $w + w_1 = m + 2$, the point $(w, w_1)$ lies on the line $x + y = m + 2$.
      use L_new
      aesop;
      norm_cast; linarith

/-
If for some integer $m \\ge 3$ there exists a set of $m$ lines covering $S_m$ with $k$ sunny lines, then there exists a set of $m+1$ lines covering $S_{m+1}$ with the same number $k$ of sunny lines.
-
-/
lemma lem_induction_step (m k : ℕ) (hm : m ≥ 3)
  (h_exists : ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = m ∧
    (∀ p ∈ s m, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = k) :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = m + 1 ∧
    (∀ p ∈ s (m+1), ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = k := by
      obtain ⟨ lines, hlines1, hlines2, hlines3, hlines4 ⟩ := h_exists;
      -- Apply the induction step to construct the set of m+1 lines.
      have h_induction_step : ∀ p ∈ s (m + 1), ∃ l ∈ lines ∪ { {v : ℝ × ℝ | v.1 + v.2 = (m : ℝ) + 2} }, p ∈ l := by
        apply lem_induction_step_coverage;
        assumption;
      by_cases h : {v : ℝ × ℝ | v.1 + v.2 = (m : ℝ) + 2} ∈ lines;
      · -- If the new line is already in the set of lines, then we can add a dummy line that does not affect the coverage of points.
        obtain ⟨dummy_line, hdummy_line⟩ : ∃ dummy_line : Set (ℝ × ℝ), ¬dummy_line ∈ lines ∧ ¬Sunny dummy_line ∧ (∃ a b c : ℝ, ¬(a = 0 ∧ b = 0) ∧ dummy_line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) := by
          -- Since there are infinitely many non-sunny lines, we can choose one that is not in the current set of lines.
          have h_inf_non_sunny : Set.Infinite {l : Set (ℝ × ℝ) | ¬Sunny l ∧ ∃ a b c : ℝ, ¬(a = 0 ∧ b = 0) ∧ l = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}} := by
            refine' Set.infinite_of_injective_forall_mem ( fun x y hxy => _ ) fun n : ℕ => show { v : ℝ × ℝ | v.1 = n + 1 } ∈ { l : Set ( ℝ × ℝ ) | ¬Sunny l ∧ ∃ a b c : ℝ, ¬ ( a = 0 ∧ b = 0 ) ∧ l = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 } } from ⟨ _, _ ⟩;
            · rw [ Set.ext_iff ] at hxy ; specialize hxy ( ( x : ℝ ) + 1, 0 ) ; aesop;
            · rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
              norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
              exact h₃ ( by linarith [ h₁.1 ( n + 1 ) 0 rfl, h₁.1 ( n + 1 ) 1 rfl ] );
            · exact ⟨ 1, 0, - ( n + 1 ), by norm_num, by ext; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> linarith ⟩;
          exact Exists.imp ( by aesop ) ( h_inf_non_sunny.exists_not_mem_finset lines );
        refine' ⟨ Insert.insert dummy_line lines, _, _, _, _ ⟩ <;> simp_all ( config := { decide := Bool.true } );
        · grind;
        · rw [ Finset.filter_insert ] ; aesop;
      · refine' ⟨ lines ∪ { { v : ℝ × ℝ | v.1 + v.2 = ( m : ℝ ) + 2 } }, _, _, _, _ ⟩;
        · simp +zetaDelta at *;
          rintro line ( hline | rfl );
          · exact hlines1 line hline;
          · exact ⟨ 1, 1, by norm_num, - ( m + 2 ), by ext; norm_num; constructor <;> intros <;> linarith ⟩;
        · rw [ Finset.card_union ] ; aesop;
        · assumption;
        · rw [ Finset.filter_union, Finset.filter_singleton ];
          rw [ if_neg ];
          · aesop;
          · rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
            norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
            exact h₄ ( by linarith [ h₁.1 ( m + 2 ) 0 ( by ring ), h₁.1 ( m + 1 ) 1 ( by ring ), h₁.1 ( m ) 2 ( by ring ) ] )

/-
For any integer $n \\ge 3$, $k=3$ is a possible value.
-
-/
lemma lem_k3_possible (n : ℕ) (hn : n ≥ 3) :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 3 := by
      -- By Lemma~\\ref{lem:induction_step}, we can construct a set of $n$ lines covering $S_n$ with $k=3$ sunny lines for any $n \\geq 3$.
      induction' n, Nat.succ_le.mpr hn using Nat.le_induction with n ih;
      · exact?;
      · -- Apply Lemma~\\ref{lem:induction_step} to construct the set of lines for $n+1$.
        apply lem_induction_step n 3 ih;
        aesop

/-
If there exists a configuration of $n$ lines covering $S_n$ with $k$ sunny lines, and one of the lines is $x=1$, $y=1$, or $x+y=n+1$, then there exists a configuration of $n-1$ lines covering $S_{n-1}$ with $k$ or $k-1$ sunny lines. If the line is non-sunny, the number of sunny lines is $k$.
-
-/
lemma lem_reduction (n k : ℕ) (hn : n ≥ 4)
  (h_exists : ∃ L : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ L, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    L.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ L, p ∈ l) ∧
    (L.filter Sunny).card = k ∧
    ({v | v.1 = (1:ℝ)} ∈ L ∨ {v | v.2 = (1:ℝ)} ∈ L ∨ {v | v.1 + v.2 = (n + 1 : ℝ)} ∈ L)) :
  ∃ L' : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ L', ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    L'.card = n - 1 ∧
    (∀ p ∈ s (n-1), ∃ l ∈ L', p ∈ l) ∧
    (L'.filter Sunny).card = k := by
      bound;
      · refine' ⟨ Finset.image ( fun l => { v : ℝ × ℝ | ∃ w ∈ l, w = ( v.1 + 1, v.2 ) } ) ( w.erase { v : ℝ × ℝ | v.1 = 1 } ), _, _, _, _ ⟩;
        · simp +zetaDelta at *;
          rintro line x hx hx' rfl;
          rcases left x hx' with ⟨ a, b, hab, c, rfl ⟩;
          exact ⟨ a, b, hab, c + a, by ext; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> linarith ⟩;
        · rw [ Finset.card_image_of_injective ];
          · -- Since {v | v.1 = 1} is in w, removing it should decrease the cardinality by 1.
            simp [Finset.card_erase_of_mem h];
          · intro l l' hl; ext x; replace hl := Set.ext_iff.mp hl ( x.1 - 1, x.2 ) ; aesop;
        · -- For any point $p \\in s (w.card - 1)$, there exists a line in $w.erase {v | v.1 = 1}$ that contains $(p.1 + 1, p.2)$.
          intro p hp
          obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp;
          -- Since $(a+1, b) \\in S_n$, there exists a line $l \\in w$ such that $(a+1, b) \\in l$.
          obtain ⟨l, hl₁, hl₂⟩ : ∃ l ∈ w, ((a + 1 : ℝ), (b : ℝ)) ∈ l := by
            exact left_2 _ ⟨ a + 1, b, by linarith, by linarith, by omega, by norm_cast ⟩;
          cases eq_or_ne l { v : ℝ × ℝ | v.1 = 1 } <;> aesop;
        · -- Since the transformation preserves the sunny property, the number of sunny lines in L' is the same as in L.
          have h_sunny_preserved : ∀ l ∈ w.erase {v : ℝ × ℝ | v.1 = 1}, Sunny l ↔ Sunny {v : ℝ × ℝ | ∃ w ∈ l, w = (v.1 + 1, v.2)} := by
            -- If a line l is sunny, then the line l' obtained by shifting l to the right by 1 is also sunny, and vice versa.
            intros l hl
            constructor;
            · rintro ⟨ a, b, c, rfl, ha, hb, hab ⟩;
              exact ⟨ a, b, c + a, by ext; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> linarith, ha, hb, by contrapose! hab; linarith ⟩;
            · rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
              use a, b, c - a;
              norm_num [ Set.ext_iff ] at *;
              exact ⟨ fun x y => by specialize h₁ ( x - 1 ) y; ring_nf at *; aesop, h₂, h₃, h₄ ⟩;
          rw [ Finset.card_filter, Finset.card_filter, Finset.sum_image ];
          · rw [ ← Finset.sum_erase_add _ _ h ] ; aesop;
            · cases h_1 ; aesop;
              rw [ Set.ext_iff ] at h_1 ; have := h_1 ( 1, 0 ) ; have := h_1 ( 1, 1 ) ; norm_num at * ; cases lt_or_gt_of_ne left_1 <;> cases lt_or_gt_of_ne left_3 <;> nlinarith;
            · exact congr_arg Finset.card ( Finset.filter_congr fun x hx => by specialize h_sunny_preserved x; aesop );
          · aesop;
            ext ⟨ a, b ⟩ ; replace a_2 := Set.ext_iff.mp a_2 ( a - 1, b ) ; aesop;
      · refine' ⟨ Finset.image ( fun l => { v : ℝ × ℝ | ∃ w ∈ l, w = ( v.1, v.2 + 1 ) } ) ( w \\ { { v : ℝ × ℝ | v.2 = 1 } } ), _, _, _, _ ⟩;
        · -- For any line in the image, we can take the original a, b, c from l and adjust c to c + b. Since a and b aren't both zero in the original line, they won't be both zero in the new line either.
          intro line hline
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hline;
          -- By hypothesis left, there exist a, b, c such that l = {v | a*v.1 + b*v.2 + c = 0} and a ≠ 0 or b ≠ 0.
          obtain ⟨a, b, c, h_ne_zero, hl_eq⟩ := left l (Finset.mem_sdiff.mp hl).left;
          exact ⟨ a, b, c + b, by aesop, by ext; aesop <;> linarith ⟩;
        · rw [ Finset.card_image_of_injective ];
          · exact Finset.card_sdiff <| Finset.singleton_subset_iff.mpr h;
          · intro l l' h; ext x; replace h := Set.ext_iff.mp h ( x.1, x.2 - 1 ) ; aesop;
        · field_simp;
          intro a b hab;
          rcases hab with ⟨ a, b, ha, hb, hab, rfl, rfl ⟩;
          specialize left_2 ( a, b + 1 );
          exact Exists.elim ( left_2 ⟨ a, b + 1, by linarith, by linarith, by omega, by aesop ⟩ ) fun l hl => ⟨ l, ⟨ hl.1, by rintro rfl; exact absurd hl.2 ( by norm_num; linarith ) ⟩, hl.2 ⟩;
        · -- Since the transformation preserves the sunny property, the number of sunny lines in the new set is the same as in the original set.
          have h_sunny_preserved : ∀ l ∈ w \\ { {v : ℝ × ℝ | v.2 = 1} }, Sunny l ↔ Sunny {v : ℝ × ℝ | ∃ w ∈ l, w = (v.1, v.2 + 1)} := by
            aesop;
            · obtain ⟨ a, b, c, rfl, ha, hb, hab ⟩ := a;
              exact ⟨ a, b, c + b, by ext; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> linarith, ha, hb, by contrapose! hab; linarith ⟩;
            · obtain ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ := a;
              use a, b, c - b;
              norm_num [ Set.ext_iff ] at *;
              exact ⟨ fun x y => by specialize h₁ x ( y - 1 ) ; ring_nf at *; aesop, h₂, h₃, h₄ ⟩;
          -- Since the transformation preserves the sunny property, the number of sunny lines in the new set is the same as in the original set. Therefore, the cardinality of the filter of sunny lines in the new set is equal to the cardinality of the filter of sunny lines in the original set.
          have h_card_eq : (Finset.filter Sunny (Finset.image (fun l => {v : ℝ × ℝ | ∃ w ∈ l, w = (v.1, v.2 + 1)}) (w \\ { {v : ℝ × ℝ | v.2 = 1} }))).card = (Finset.filter Sunny (w \\ { {v : ℝ × ℝ | v.2 = 1} })).card := by
            rw [ Finset.card_filter, Finset.card_filter, Finset.sum_image ];
            · exact Finset.sum_congr rfl fun x hx => by specialize h_sunny_preserved x hx; aesop;
            · aesop;
              ext ⟨ a, b ⟩ ; replace a_2 := Set.ext_iff.mp a_2 ( a, b - 1 ) ; aesop;
          -- Since the line $y=1$ is non-sunny, removing it from $w$ does not change the count of sunny lines.
          have h_non_sunny : ¬Sunny {v : ℝ × ℝ | v.2 = 1} := by
            rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
            norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
            exact h₂ ( by linarith [ h₁.1 0, h₁.1 1 ] );
          rw [ h_card_eq, Finset.card_filter, Finset.card_filter, Finset.sum_eq_sum_diff_singleton_add h ] ; aesop;
      · -- Let's remove the line $x + y = n + 1$ from $w$ and show that the remaining lines cover $S_{n-1}$.
        set L' := w \\ { {v : ℝ × ℝ | v.1 + v.2 = (w.card : ℝ) + 1} };
        refine' ⟨ L', _, _, _, _ ⟩;
        · aesop;
        · rw [ Finset.card_sdiff ] <;> aesop;
        · -- Since $w$ covers $s w.card$, which includes all points up to $a + b = w.card + 1$, removing the line $x + y = w.card + 1$ should leave the remaining lines covering $s (w.card - 1)$.
          intros p hp
          obtain ⟨l, hl₁, hl₂⟩ := left_2 p (by
          rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact ⟨ a, b, ha, hb, by omega, rfl ⟩);
          simp +zetaDelta at *;
          rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩;
          exact ⟨ l, ⟨ hl₁, by rintro rfl; exact absurd hl₂ ( by norm_num; linarith [ show ( a : ℝ ) + b ≤ w.card by norm_cast; omega ] ) ⟩, hl₂ ⟩;
        · -- Since the line $x + y = n + 1$ is non-sunny, removing it from $w$ does not change the set of sunny lines.
          have h_non_sunny : ¬Sunny {v : ℝ × ℝ | v.1 + v.2 = (w.card : ℝ) + 1} := by
            rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
            norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
            exact h₄ ( by linarith [ h₁.1 ( ↑w.card + 1 ) 0 ( by ring ), h₁.1 0 ( ↑w.card + 1 ) ( by ring ), h₁.1 1 ( ↑w.card ) ( by ring ) ] );
          rw [ Finset.card_filter, Finset.card_filter, Finset.sum_eq_sum_diff_singleton_add h_2 ] ; aesop

/-
If a set $\\mathcal{L}$ of $n$ lines covers $S_n$ for $n \\ge 3$, and none of the lines $x=1$, $y=1$, or $x+y=n+1$ are in $\\mathcal{L}$, then all $n$ lines in $\\mathcal{L}$ must be sunny.
-
-/
lemma lem_boundary_lines_implication (n : ℕ) (hn : n ≥ 3)
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = n)
  (h_lines : ∀ l ∈ L, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ l = { v | a * v.1 + b * v.2 + c = 0 })
  (h_cover : ∀ p ∈ s n, ∃ l ∈ L, p ∈ l)
  (h_boundary : {v | v.1 = (1:ℝ)} ∉ L ∧ {v | v.2 = (1:ℝ)} ∉ L ∧ {v | v.1 + v.2 = (n + 1 : ℝ)} ∉ L) :
  ∀ l ∈ L, Sunny l := by
    -- For any line $l \\in L$, we need to show that it is not parallel to the $x$-axis, $y$-axis, or the line $x+y=0$.
    have h_not_parallel : ∀ l ∈ L, ¬(∃ c : ℝ, l = {v : ℝ × ℝ | v.1 = c}) ∧ ¬(∃ c : ℝ, l = {v : ℝ × ℝ | v.2 = c}) ∧ ¬(∃ c : ℝ, l = {v : ℝ × ℝ | v.1 + v.2 = c}) := by
      bound;
      · -- If $x = w$ is in $L$, then for each $j \\in \\{1, 2, \\ldots, n\\}$, the point $(1, j)$ must be covered by some line in $L$.
        have h_cover : ∀ j : ℕ, 1 ≤ j → j ≤ L.card → ∃ l ∈ L, l ≠ {v : ℝ × ℝ | v.1 = w} ∧ ((1 : ℝ), (j : ℝ)) ∈ l := by
          -- Since $(1, j)$ is in $s L.card$, by $h_cover$, there exists a line in $L$ that contains $(1, j)$.
          have h_exists_line : ∀ j : ℕ, 1 ≤ j → j ≤ L.card → ∃ l ∈ L, ((1 : ℝ), (j : ℝ)) ∈ l := by
            exact fun j hj₁ hj₂ => h_cover _ ⟨ 1, j, by norm_num, by linarith, by linarith, by norm_num ⟩;
          intro j hj₁ hj₂; specialize h_exists_line j hj₁ hj₂; aesop;
        -- By the pigeonhole principle, since there are L.card points (1, j) and only L.card - 1 other lines in L, at least two of these points must be covered by the same line.
        have h_pigeonhole : ∃ j k : ℕ, 1 ≤ j ∧ j ≤ L.card ∧ 1 ≤ k ∧ k ≤ L.card ∧ j ≠ k ∧ ∃ l ∈ L, l ≠ {v : ℝ × ℝ | v.1 = w} ∧ ((1 : ℝ), (j : ℝ)) ∈ l ∧ ((1 : ℝ), (k : ℝ)) ∈ l := by
          choose! f hf using h_cover;
          have h_pigeonhole : Finset.card (Finset.image f (Finset.Icc 1 L.card)) ≤ L.card - 1 := by
            have h_distinct : Finset.image f (Finset.Icc 1 L.card) ⊆ L \\ { {v : ℝ × ℝ | v.1 = w} } := by
              simp_all ( config := { decide := Bool.true } ) [ Finset.image_subset_iff ];
            exact le_trans ( Finset.card_le_card h_distinct ) ( by rw [ Finset.card_sdiff ] <;> aesop );
          contrapose! h_pigeonhole;
          rw [ Finset.card_image_of_injOn ];
          · simp;
            exact ⟨ _, a ⟩;
          · field_simp;
            exact fun x hx y hy hxy => Classical.not_not.1 fun h => h_pigeonhole x y hx.1 hx.2 hy.1 hy.2 h ( f x ) ( hf x hx.1 hx.2 |>.1 ) ( hf x hx.1 hx.2 |>.2.1 ) ( hf x hx.1 hx.2 |>.2.2 ) ( by simpa [ hxy ] using hf y hy.1 hy.2 |>.2.2 );
        bound;
        obtain ⟨ a, b, c, h, rfl ⟩ := h_lines _ left_7;
        simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
      · -- Since $y = w$ is in $L$, it must cover some point $(a, 1)$ for $a \\in \\{1, 2, \\ldots, n\\}$.
        have h_cover_y1 : ∀ a ∈ Finset.Icc 1 L.card, ∃ l ∈ L, l ≠ {v : ℝ × ℝ | v.2 = w} ∧ ((a : ℝ), 1) ∈ l := by
          intro a ha;
          have := h_cover ( a, 1 ) ⟨ a, 1, by linarith [ Finset.mem_Icc.mp ha ], by norm_num, by linarith [ Finset.mem_Icc.mp ha ], by norm_num ⟩;
          exact this.imp fun l hl => ⟨ hl.1, by rintro rfl; exact absurd hl.2 ( by norm_num; aesop ), hl.2 ⟩;
        -- By the pigeonhole principle, since there are L.card a's and only L.card - 1 other lines, at least two of these a's must be covered by the same line.
        have h_pigeonhole : ∃ a b : ℕ, a ∈ Finset.Icc 1 L.card ∧ b ∈ Finset.Icc 1 L.card ∧ a ≠ b ∧ ∃ l ∈ L, l ≠ {v : ℝ × ℝ | v.2 = w} ∧ ((a : ℝ), 1) ∈ l ∧ ((b : ℝ), 1) ∈ l := by
          choose! f hf using h_cover_y1;
          have h_pigeonhole : Finset.card (Finset.image f (Finset.Icc 1 L.card)) ≤ L.card - 1 := by
            have h_distinct : Finset.image f (Finset.Icc 1 L.card) ⊆ L \\ { {v : ℝ × ℝ | v.2 = w} } := by
              simp_all ( config := { decide := Bool.true } ) [ Finset.image_subset_iff ];
            exact le_trans ( Finset.card_le_card h_distinct ) ( by rw [ Finset.card_sdiff ] <;> aesop );
          contrapose! h_pigeonhole;
          rw [ Finset.card_image_of_injOn ];
          · field_simp;
          · exact fun a ha b hb hab => Classical.not_not.1 fun h => h_pigeonhole a b ha hb h ( f a ) ( hf a ha |>.1 ) ( hf a ha |>.2.1 ) ( hf a ha |>.2.2 ) ( by simpa [ hab ] using hf b hb |>.2.2 );
        simp +zetaDelta at *;
        obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩, hab, l, hl₁, hl₂, hl₃, hl₄ ⟩ := h_pigeonhole;
        obtain ⟨ a', b', hab', x', rfl ⟩ := h_lines l hl₁;
        simp_all ( config := { decide := Bool.true } );
        by_cases ha : a' = 0;
        · simp_all ( config := { decide := Bool.true } ) [ add_eq_zero_iff_eq_neg ];
        · exact hab ( Nat.cast_injective ( mul_left_cancel₀ ha <| by linarith : ( a : ℝ ) = b ) );
      · -- Since $x + y = w$ is in $L$ and $w \\neq n + 1$, this line cannot cover any point $(a, b)$ with $a + b = n + 1$.
        have h_cover_false : ∀ a ∈ Finset.Icc 1 (L.card), ∃ l ∈ L, ((a : ℝ), (L.card + 1 - a : ℝ)) ∈ l ∧ l ≠ {v : ℝ × ℝ | v.1 + v.2 = w} := by
          -- Since $a + (L.card + 1 - a) = L.card + 1$, the point $(a, L.card + 1 - a)$ is in $s L.card$.
          have h_point_in_sn : ∀ a ∈ Finset.Icc 1 L.card, ((a : ℝ), (L.card + 1 - a : ℝ)) ∈ s L.card := by
            -- By definition of $s$, we need to show that for any $a \\in \\{1, 2, \\ldots, L.card\\}$, the point $(a, L.card + 1 - a)$ satisfies $a + (L.card + 1 - a) \\leq L.card + 1$.
            intro a ha
            use a, L.card + 1 - a;
            norm_num +zetaDelta at *;
            exact ⟨ ha.1, Nat.lt_succ_of_le ha.2, by omega, by rw [ Nat.cast_sub ] <;> norm_num ; linarith ⟩;
          -- By h_cover, for each $a \\in \\{1, 2, \\ldots, L.card\\}$, there exists a line in $L$ that contains the point $(a, L.card + 1 - a)$.
          have h_cover_exists : ∀ a ∈ Finset.Icc 1 L.card, ∃ l ∈ L, ((a : ℝ), (L.card + 1 - a : ℝ)) ∈ l := by
            exact fun a ha => h_cover _ ( h_point_in_sn a ha );
          intro a ha; specialize h_cover_exists a ha; obtain ⟨ l, hl₁, hl₂ ⟩ := h_cover_exists; use l; aesop;
        choose! f hf using h_cover_false;
        have h_distinct : Finset.card (Finset.image f (Finset.Icc 1 L.card)) ≤ Finset.card L - 1 := by
          have h_distinct : Finset.image f (Finset.Icc 1 L.card) ⊆ L \\ { {v : ℝ × ℝ | v.1 + v.2 = w} } := by
            simp_all ( config := { decide := Bool.true } ) [ Finset.image_subset_iff ];
          exact le_trans ( Finset.card_le_card h_distinct ) ( by rw [ Finset.card_sdiff ] <;> aesop );
        rw [ Finset.card_image_of_injOn ] at h_distinct;
        · norm_num at * ; omega;
        · intros x hx y hy; have := hf x hx; have := hf y hy; aesop;
          cases h_lines _ ( hf x left_2 right_1 |>.1 ) ; aesop;
          have := hf y left_3 right_2; aesop;
          by_cases hw : w_1 = w_2;
          · aesop;
            exact False.elim <| right <| by convert left_5 using 1; ext ; simp ( config := { decide := Bool.true } ) ; constructor <;> intros <;> cases lt_or_gt_of_ne left_4 <;> nlinarith;
          · exact_mod_cast ( mul_left_cancel₀ ( sub_ne_zero_of_ne hw ) <| by linarith : ( x : ℝ ) = y );
    -- By definition of sunny, if a line is not parallel to the x-axis, y-axis, or x+y=0, then it must be sunny.
    intros l hl
    obtain ⟨a, b, c, h_ne_zero, h_eq⟩ := h_lines l hl;
    use a, b, c;
    -- Since $l$ is not parallel to the $x$-axis or $y$-axis, $a$ and $b$ cannot be zero.
    have h_a_ne_zero : a ≠ 0 := by
      -- If $a = 0$, then the line equation becomes $b * y + c = 0$, which is a horizontal line. However, $h_not_parallel$ states that the line cannot be parallel to the $x$-axis, which means it cannot be horizontal. Therefore, $a$ must be non-zero.
      by_contra ha_zero
      have h_horizontal : ∃ c : ℝ, l = {v : ℝ × ℝ | v.2 = c} := by
        exact ⟨ -c / b, by ext; simp ( config := { decide := Bool.true } ) [ h_eq, ha_zero, field_simps, show b ≠ 0 by aesop ] ; constructor <;> intros <;> linarith ⟩;
      exact h_not_parallel l hl |>.2.1 h_horizontal
    have h_b_ne_zero : b ≠ 0 := by
      rintro rfl;
      exact h_not_parallel l hl |>.1 ⟨ -c / a, by ext; simp ( config := { decide := Bool.true } ) [ h_eq, field_simps, h_a_ne_zero ] ; constructor <;> intros <;> linarith ⟩;
    bound;
    exact h_not_parallel _ hl |>.2.2 ⟨ -c / a, by ext ⟨ x, y ⟩ ; simpa [ field_simps, h_b_ne_zero ] using by constructor <;> intros <;> linarith ⟩

/-
Let $n \\ge 3$. If a set $\\mathcal{L}$ of $n$ sunny lines covers $S_n$, then one line in $\\mathcal{L}$, call it $L_1$, passes through $(1,1)$. The other $n-1$ lines in $\\mathcal{L}$ establish a bijection between the sets of points $\\{(1,j): j=2,\\dots,n\\}$ and $\\{(i,1): i=2,\\dots,n\\}$.
-
-/
lemma lem_kn_setup (n : ℕ) (hn : n ≥ 3)
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = n) (h_sunny : ∀ l ∈ L, Sunny l)
  (h_cover : ∀ p ∈ s n, ∃ l ∈ L, p ∈ l) :
  ∃ L1 ∈ L, ((1:ℝ), (1:ℝ)) ∈ L1 ∧
    (let PtsX := Finset.image (fun j : ℕ => ((1:ℝ), (j:ℝ))) (Finset.Icc (2:ℕ) n);
    let PtsY := Finset.image (fun i : ℕ => ((i:ℝ), (1:ℝ))) (Finset.Icc (2:ℕ) n);
    ∀ l ∈ L \\ {L1}, (∃! p ∈ PtsX, p ∈ l) ∧ (∃! q ∈ PtsY, q ∈ l)) := by
      -- Let's first show that there exists a line $L_1 \\in \\mathcal{L}$ passing through $(1,1)$.
      obtain ⟨L1, hL1_in, hL1_cover⟩ : ∃ L1 ∈ L, ((1:ℝ), (1:ℝ)) ∈ L1 := by
        -- By definition of $s$, we know that $(1, 1) \\in s n$ since $1 + 1 \\leq n + 1$ for $n \\geq 3$.
        have h_point_in_sn : (1, 1) ∈ s n := by
          exact ⟨ 1, 1, by norm_num, by norm_num, by linarith, by norm_num ⟩;
        exact h_cover _ h_point_in_sn;
      -- Since $L$ is a set of sunny lines, each line in $L \\setminus \\{L1\\}$ must intersect $PtsX$ and $PtsY$ exactly once.
      have h_inter : ∀ l ∈ L \\ {L1}, (∃ p ∈ Finset.image (fun j : ℕ => ((1 : ℝ), (j : ℝ))) (Finset.Icc 2 n), p ∈ l) ∧ (∃ q ∈ Finset.image (fun i : ℕ => ((i : ℝ), (1 : ℝ))) (Finset.Icc 2 n), q ∈ l) := by
        aesop;
        · -- Since $l$ is a sunny line, it must intersect the line $x=1$ at some point $(1, a)$ where $a \\in \\{2, 3, \\ldots, n\\}$.
          have h_inter_x : ∃ a ∈ Finset.Icc 2 (L.card), (1, (a : ℝ)) ∈ l := by
            -- By the coverage condition, for each $j \\in \\{2, 3, \\ldots, L.card\\}$, there exists a line in $L$ that contains $(1, j)$. Since $l \\in L$ and $l \\neq L1$, it must contain some $(1, j)$ where $j \\in \\{2, 3, \\ldots, L.card\\}$.
            have h_cover_x : ∀ j ∈ Finset.Icc 2 L.card, ∃ l ∈ L, (1, (j : ℝ)) ∈ l := by
              exact fun j hj => h_cover 1 j ⟨ 1, j, by norm_num, by linarith [ Finset.mem_Icc.mp hj ], by linarith [ Finset.mem_Icc.mp hj ], by norm_num ⟩;
            choose! f hf using h_cover_x;
            -- Since $f$ is injective and $L$ has $L.card$ elements, and $l$ is in $L$, there must be some $j$ such that $f j = l$.
            have h_inj : Finset.card (Finset.image f (Finset.Icc 2 L.card)) = L.card - 1 := by
              rw [ Finset.card_image_of_injOn ];
              · simp;
              · intros x hx y hy; have := hf x hx; have := hf y hy; aesop;
                cases h_sunny _ ( hf x left_1 right_1 |>.1 ) ; aesop;
                have := hf y left_2 right_2; aesop;
                exact_mod_cast ( mul_left_cancel₀ left_4 <| by linarith : ( x : ℝ ) = y );
            have h_inj : Finset.image f (Finset.Icc 2 L.card) = L \\ {L1} := by
              apply Finset.eq_of_subset_of_card_le;
              · intro; aesop;
                have := hf w left_1 right_2; specialize hf w left_1 right_2; rcases h_sunny _ this.1 with ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ ; simp_all ( config := { decide := Bool.true } ) [ Set.ext_iff ];
                exact h₃ ( by nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ w ) ] );
              · rw [ Finset.card_sdiff ] <;> aesop;
            replace h_inj := Finset.ext_iff.mp h_inj l; aesop;
          aesop;
        · -- Since $L$ covers all points in $S_n$, including $(i, 1)$ for $i \\in \\{2, \\dots, n\\}$, and $L1$ covers $(1, 1)$, the remaining lines in $L \\setminus \\{L1\\}$ must cover the points $(i, 1)$ for $i \\in \\{2, \\dots, n\\}$.
          have h_cover_remaining : ∀ i ∈ Finset.Icc 2 (L.card), ∃ l ∈ L \\ {L1}, ((i : ℝ), 1) ∈ l := by
            -- Since $L$ covers all points in $S_n$, including $(i, 1)$ for $i \\in \\{2, \\dots, L.card\\}$, and $L1$ covers $(1, 1)$, the remaining lines in $L \\setminus \\{L1\\}$ must cover the points $(i, 1)$ for $i \\in \\{2, \\dots, L.card\\}$.
            intros i hi
            obtain ⟨l, hlL, hl⟩ : ∃ l ∈ L, ((i : ℝ), 1) ∈ l := by
              exact h_cover i 1 ⟨ i, 1, by linarith [ Finset.mem_Icc.mp hi ], by norm_num, by linarith [ Finset.mem_Icc.mp hi ], by norm_num ⟩;
            by_cases hl1 : l = L1;
            · rcases h_sunny L1 hL1_in with ⟨ a, b, c, rfl, ha, hb, hab ⟩;
              simp_all ( config := { decide := Bool.true } );
              exact False.elim <| ha <| by nlinarith [ ( by norm_cast; linarith : ( 2 : ℝ ) ≤ i ) ] ;
            · aesop;
          choose! f hf using h_cover_remaining;
          have h_image : Finset.image f (Finset.Icc 2 (L.card)) = L \\ {L1} := by
            apply Finset.eq_of_subset_of_card_le;
            · exact Finset.image_subset_iff.mpr fun i hi => hf i hi |>.1;
            · rw [ Finset.card_image_of_injOn ];
              · rw [ Finset.card_sdiff ] <;> aesop;
              · intros i hi j hj hij;
                have := hf i hi; have := hf j hj; aesop;
                cases h_sunny _ ( hf j left_2 right_2 |>.1.1 ) ; aesop;
                have := hf j left_2 right_2; aesop;
                exact_mod_cast ( mul_left_cancel₀ left_3 <| by linarith : ( i : ℝ ) = j );
          replace h_image := Finset.ext_iff.mp h_image l; aesop;
      -- Since $L$ is a set of sunny lines, each line in $L \\setminus \\{L1\\}$ cannot be parallel to the x-axis, y-axis, or the line $x+y=0$.
      have h_not_parallel : ∀ l ∈ L \\ {L1}, ∀ p q : ℝ × ℝ, p ∈ Finset.image (fun j : ℕ => ((1 : ℝ), (j : ℝ))) (Finset.Icc 2 n) → q ∈ Finset.image (fun j : ℕ => ((1 : ℝ), (j : ℝ))) (Finset.Icc 2 n) → p ∈ l → q ∈ l → p = q ∧ ∀ p q : ℝ × ℝ, p ∈ Finset.image (fun i : ℕ => ((i : ℝ), (1 : ℝ))) (Finset.Icc 2 n) → q ∈ Finset.image (fun i : ℕ => ((i : ℝ), (1 : ℝ))) (Finset.Icc 2 n) → p ∈ l → q ∈ l → p = q := by
        aesop;
        · cases h_sunny l left ; aesop;
          exact mul_left_cancel₀ left_4 <| by linarith;
        · cases h_sunny l left ; aesop;
          exact_mod_cast ( mul_left_cancel₀ left_3 <| by linarith : ( x : ℝ ) = x_1 );
      -- By combining h_inter and h_not_parallel, we can conclude that for each l in L \\ {L1}, there exists a unique point in PtsX and a unique point in PtsY that lie on l.
      have h_unique : ∀ l ∈ L \\ {L1}, (∃! p : ℝ × ℝ, p ∈ Finset.image (fun j : ℕ => ((1 : ℝ), (j : ℝ))) (Finset.Icc 2 n) ∧ p ∈ l) ∧ (∃! q : ℝ × ℝ, q ∈ Finset.image (fun i : ℕ => ((i : ℝ), (1 : ℝ))) (Finset.Icc 2 n) ∧ q ∈ l) := by
        intro l hl;
        bound;
        · obtain ⟨ p, hp₁, hp₂ ⟩ := h_inter l hl |>.1;
          exact ⟨ p, ⟨ hp₁, hp₂ ⟩, fun q hq => h_not_parallel l hl q p hq.1 hp₁ hq.2 hp₂ |>.1 ⟩;
        · obtain ⟨ q, hq₁, hq₂ ⟩ := h_inter l hl |>.2;
          use q;
          grind;
      exact ⟨ L1, hL1_in, hL1_cover, h_unique ⟩

/-
Let $n \\ge 3$. If a set $\\mathcal{L}$ of $n$ sunny lines covers $S_n$, let $L_1$ be the line covering $(1,1)$. For each $j \\in \\{2,\\dots,n\\}$, there is a unique line $L_j \\in \\mathcal{L} \\setminus \\{L_1\\}$ that passes through $(1,j)$. This induces a permutation $\\sigma$ of $\\{2,\\dots,n\\}$ such that $L_j$ also passes through $(\\sigma(j),1)$.
-
-/
lemma lem_kn_permutation_setup (n : ℕ) (hn : n ≥ 3)
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = n) (h_sunny : ∀ l ∈ L, Sunny l)
  (h_cover : ∀ p ∈ s n, ∃ l ∈ L, p ∈ l)
  (L1 : Set (ℝ × ℝ)) (h_L1_in : L1 ∈ L) (h_L1_covers_1_1 : ((1:ℝ), (1:ℝ)) ∈ L1) :
  ∃ σ : Equiv.Perm {i // i ∈ Finset.Icc (2:ℕ) n},
    ∀ (j : {i // i ∈ Finset.Icc (2:ℕ) n}), ∃! l ∈ L \\ {L1}, ((1:ℝ), (j:ℝ)) ∈ l ∧ ((((σ j):ℕ):ℝ), (1:ℝ)) ∈ l := by
      -- Let's denote the set of points $(1, j)$ for $j \\in \\{2, \\ldots, n\\}$ as $PtsX$ and the set of points $(i, 1)$ for $i \\in \\{2, \\ldots, n\\}$ as $PtsY$.
      set PtsX := Finset.image (fun j : ℕ => ((1:ℝ), (j:ℝ))) (Finset.Icc (2:ℕ) n)
      set PtsY := Finset.image (fun i : ℕ => ((i:ℝ), (1:ℝ))) (Finset.Icc (2:ℕ) n);
      have h_bijection : ∀ j : Finset.Icc (2:ℕ) n, ∃! l ∈ L \\ {L1}, ((1:ℝ), (j:ℝ)) ∈ l := by
        intro j;
        have h_unique_line : ∀ j : Finset.Icc (2:ℕ) n, ∃ l ∈ L, ((1:ℝ), (j:ℝ)) ∈ l ∧ l ≠ L1 := by
          intro j;
          obtain ⟨ l, hl₁, hl₂ ⟩ := h_cover ( 1, j ) ⟨ 1, j, by norm_num, by linarith [ Finset.mem_Icc.mp j.2 ], by linarith [ Finset.mem_Icc.mp j.2 ], by norm_num ⟩;
          by_cases hl₃ : l = L1;
          · rcases h_sunny L1 h_L1_in with ⟨ a, b, c, rfl, ha, hb, hab ⟩;
            -- Subtracting the equation $a + b + c = 0$ from $a + b*j + c = 0$ gives $b*(j-1) = 0$. Since $b \\neq 0$, this implies $j = 1$, which contradicts $j \\geq 2$.
            have h_contra : b * (j - 1) = 0 := by
              aesop;
              exact mul_left_cancel₀ hb <| by linarith;
            exact absurd h_contra ( mul_ne_zero hb ( sub_ne_zero_of_ne ( by norm_cast; linarith [ Finset.mem_Icc.mp j.2 ] ) ) );
          · exact ⟨ l, hl₁, hl₂, hl₃ ⟩;
        choose f hf using h_unique_line;
        have h_unique_line : Finset.image f Finset.univ = L \\ {L1} := by
          apply Finset.eq_of_subset_of_card_le;
          · simp_all ( config := { decide := Bool.true } ) [ Finset.image_subset_iff ];
          · rw [ Finset.card_image_of_injective ];
            · rw [ Finset.card_sdiff ] <;> aesop;
            · intros x y hxy;
              have := hf x; have := hf y; aesop;
              cases h_sunny _ left ; aesop;
              exact_mod_cast ( mul_left_cancel₀ left_4 <| by linarith : ( val_1 : ℝ ) = val_2 );
        use f j;
        aesop;
        · exact hf _ ( Finset.mem_Icc.mp property ) |>.1;
        · specialize hf val ( Finset.mem_Icc.mp property );
          grind;
        · exact hf val ( Finset.mem_Icc.mp property ) |>.2.1;
        · replace h_unique_line := Finset.ext_iff.mp h_unique_line y; aesop;
          cases h_sunny _ ( hf _ ⟨ left, right ⟩ |>.1 ) ; aesop;
          have := hf w ⟨ left, right ⟩ ; aesop;
          simp_all ( config := { decide := Bool.true } ) [ show val = w by exact_mod_cast ( mul_left_cancel₀ left_2 <| by linarith : ( val : ℝ ) = w ) ];
      -- Since these lines are distinct and cover all points (i, 1) for i in {2, ..., n}, they form a bijection between the sets {2, ..., n} and {2, ..., n}.
      have h_bijection : ∀ i : Finset.Icc (2:ℕ) n, ∃! l ∈ L \\ {L1}, ((i:ℝ), (1:ℝ)) ∈ l := by
        have h_bijection : ∀ i : Finset.Icc (2:ℕ) n, ∃ l ∈ L \\ {L1}, ((i:ℝ), (1:ℝ)) ∈ l := by
          have h_cover : ∀ i : Finset.Icc (2:ℕ) n, ∃ l ∈ L, ((i:ℝ), (1:ℝ)) ∈ l := by
            intro i;
            convert h_cover ( i, 1 ) _;
            exact ⟨ i, 1, by linarith [ Finset.mem_Icc.mp i.2 ], by norm_num, by linarith [ Finset.mem_Icc.mp i.2 ], by norm_num ⟩
          intro i;
          obtain ⟨ l, hl₁, hl₂ ⟩ := h_cover i;
          by_cases hl₃ : l = L1;
          · rcases h_sunny L1 h_L1_in with ⟨ a, b, c, rfl, ha, hb, hab ⟩;
            simp_all ( config := { decide := Bool.true } );
            exact False.elim <| ha <| by nlinarith [ show ( i : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp i.2 ] ] ;
          · exact ⟨ l, Finset.mem_sdiff.mpr ⟨ hl₁, by aesop ⟩, hl₂ ⟩;
        choose f hf using h_bijection;
        have h_bijection : Finset.image f Finset.univ = L \\ {L1} := by
          apply Finset.eq_of_subset_of_card_le;
          · exact Finset.image_subset_iff.mpr fun i _ => hf i |>.1;
          · rw [ Finset.card_image_of_injective ];
            · rw [ Finset.card_sdiff ] <;> aesop;
            · intros i j hij;
              have := hf i; have := hf j; aesop;
              cases h_sunny _ left ; aesop;
              exact_mod_cast ( mul_left_cancel₀ left_1 <| by linarith : ( val : ℝ ) = val_1 );
        -- Since $f$ is injective, each line in $L \\setminus \\{L1\\}$ corresponds to exactly one $i$.
        have h_injective : Function.Injective f := by
          intros i j hij;
          have := hf i; have := hf j; aesop;
          cases h_sunny _ left ; aesop;
          exact_mod_cast ( mul_left_cancel₀ left_1 <| by linarith : ( val : ℝ ) = val_1 );
        intro i;
        refine' ⟨ f i, hf i, fun l hl => _ ⟩;
        replace h_bijection := Finset.ext_iff.mp h_bijection l; aesop;
        cases h_sunny _ ( hf _ ⟨ left_1, right_2 ⟩ |>.1.1 ) ; aesop;
        have := hf w ⟨ left_1, right_2 ⟩ ; aesop;
        cases eq_or_ne val w <;> simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
        exact False.elim <| ‹¬val = w› <| Nat.cast_injective ( mul_left_cancel₀ left <| by linarith : ( val : ℝ ) = w );
      choose σ hσ₁ hσ₂ using ‹∀ j : Finset.Icc ( 2 : ℕ ) n, ∃! l : Set ( ℝ × ℝ ), l ∈ L \\ { L1 } ∧ ( 1, ( j : ℝ ) ) ∈ l›;
      choose f hf using h_bijection;
      -- Since σ and f are both bijections, we can define a permutation σ' that maps each j to the unique i such that σ j = f i.
      obtain ⟨σ', hσ'⟩ : ∃ σ' : Equiv.Perm (Finset.Icc (2:ℕ) n), ∀ j : Finset.Icc (2:ℕ) n, σ j = f (σ' j) := by
        have h_bijection : ∀ j : Finset.Icc (2:ℕ) n, ∃ i : Finset.Icc (2:ℕ) n, σ j = f i := by
          have h_bijection : Finset.image σ Finset.univ = Finset.image f Finset.univ := by
            have h_bijection : Finset.image σ Finset.univ = L \\ {L1} ∧ Finset.image f Finset.univ = L \\ {L1} := by
              constructor;
              · apply Finset.eq_of_subset_of_card_le;
                · exact Finset.image_subset_iff.mpr fun x _ => hσ₁ x |>.1;
                · norm_num +zetaDelta at *;
                  rw [ Finset.card_image_of_injective ];
                  · simp ( config := { decide := Bool.true } ) [ Finset.card_sdiff, * ];
                  · intros a b hab;
                    have := hσ₁ a ( Finset.mem_Icc.mp a.2 ) ; have := hσ₁ b ( Finset.mem_Icc.mp b.2 ) ; aesop;
                    cases h_sunny _ left ; aesop;
                    exact_mod_cast ( mul_left_cancel₀ left_2 <| by linarith : ( val : ℝ ) = val_1 );
              · -- Since $f$ is a bijection between the universal set and $L \\setminus \\{L1\\}$, the image of $f$ must be exactly $L \\setminus \\{L1\\}$.
                have h_bijection : Finset.card (Finset.image f Finset.univ) = Finset.card (L \\ {L1}) := by
                  field_simp;
                  rw [ Finset.card_image_of_injective ];
                  · simp +zetaDelta at *;
                    rw [ Finset.card_sdiff ] <;> aesop;
                  · intros i j hij;
                    -- Since $f i = f j$, both $i$ and $j$ must be the same because the line is unique.
                    have h_unique : ∀ l ∈ L \\ {L1}, ∀ i j : Finset.Icc (2:ℕ) n, ((i:ℝ), (1:ℝ)) ∈ l → ((j:ℝ), (1:ℝ)) ∈ l → i = j := by
                      norm_num +zetaDelta at *;
                      intro l hl hl' a ha₁ ha₂ b hb₁ hb₂ ha₃ hb₃; specialize h_sunny l hl; rcases h_sunny with ⟨ a', b', c', rfl, ha₄, hb₄, hab ⟩ ; norm_num at *;
                      exact_mod_cast ( mul_left_cancel₀ ha₄ <| by linarith : ( a : ℝ ) = b );
                    exact h_unique _ ( hf i |>.1.1 ) _ _ ( hf i |>.1.2 ) ( hij ▸ hf j |>.1.2 );
                exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hf i |>.1.1 ) h_bijection.ge;
            rw [h_bijection.left, h_bijection.right];
          intro j;
          -- Since the images of σ and f are equal, for each j, there must be an i such that σ j = f i.
          have h_exists_i : ∀ j : Finset.Icc (2:ℕ) n, ∃ i : Finset.Icc (2:ℕ) n, σ j = f i := by
            intro j
            have h_in_image : σ j ∈ Finset.image f Finset.univ := by
              exact h_bijection ▸ Finset.mem_image_of_mem σ ( Finset.mem_univ j )
            simpa [ eq_comm ] using Finset.mem_image.mp h_in_image;
          exact h_exists_i j;
        choose σ' hσ' using h_bijection;
        have h_bijection : Function.Injective σ' := by
          intros j j' hj;
          have := hσ₁ j; have := hσ₁ j'; simp_all ( config := { decide := Bool.true } ) ;
          cases h_sunny _ ( by tauto ) ; aesop;
          -- Since σ ⟨val, property⟩ = σ ⟨val_1, property_1⟩, and σ is injective, we have val = val_1.
          have h_inj : σ ⟨val, property⟩ = σ ⟨val_1, property_1⟩ → val = val_1 := by
            intros h; cases h_sunny _ left; aesop;
            exact_mod_cast ( mul_left_cancel₀ left_4 <| by linarith : ( val : ℝ ) = val_1 );
          -- Since σ' ⟨val, property⟩ = σ' ⟨val_1, property_1⟩, we can use hσ' to conclude that σ ⟨val, property⟩ = σ ⟨val_1, property_1⟩.
          have h_eq : σ ⟨val, property⟩ = σ ⟨val_1, property_1⟩ := by
            rw [ hσ', hσ', hj ];
            · exact Finset.mem_Icc.mp property_1;
            · exact Finset.mem_Icc.mp property;
          exact h_inj h_eq;
        exact ⟨ Equiv.ofBijective σ' ⟨ h_bijection, Finite.injective_iff_surjective.mp h_bijection ⟩, hσ' ⟩;
      use σ';
      intro j;
      use σ j;
      grind

/-
The permutation $\\sigma$ from Lemma~\\ref{lem:kn_permutation_setup} must be a derangement, i.e., $\\sigma(j) \\ne j$ for all $j \\in \\{2, \\dots, n\\}$.
-
-/
lemma lem_kn_derangement (n : ℕ) (hn : n ≥ 3)
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = n) (h_sunny : ∀ l ∈ L, Sunny l)
  (h_cover : ∀ p ∈ s n, ∃ l ∈ L, p ∈ l)
  (L1 : Set (ℝ × ℝ)) (h_L1_in : L1 ∈ L) (h_L1_covers_1_1 : ((1:ℝ), (1:ℝ)) ∈ L1)
  (σ : Equiv.Perm {i // i ∈ Finset.Icc (2:ℕ) n})
  (h_sigma_prop : ∀ (j : {i // i ∈ Finset.Icc (2:ℕ) n}), ∃! l ∈ L \\ {L1}, ((1:ℝ), (j:ℝ)) ∈ l ∧ ((((σ j):ℕ):ℝ), (1:ℝ)) ∈ l) :
  ∀ (j : {i // i ∈ Finset.Icc (2:ℕ) n}), σ j ≠ j := by
    intro j hj;
    obtain ⟨ l, hl₁, hl₂ ⟩ := ExistsUnique.exists ( h_sigma_prop j );
    obtain ⟨ a, b, c, rfl, ha, hb, hab ⟩ := h_sunny l ( Finset.mem_sdiff.mp hl₁ |>.1 );
    simp_all ( config := { decide := Bool.true } );
    exact hab ( by nlinarith [ show ( j : ℝ ) ≥ 2 by exact_mod_cast Finset.mem_Icc.mp j.2 |>.1 ] )

/-
For $j \\in \\{2, \\dots, n\\}$, the line $L_j$ from Lemma~\\ref{lem:kn_permutation_setup} has the equation $x(j-1) + y(\\sigma(j)-1) = j\\sigma(j)-1$.
-
-/
lemma lem_kn_line_equation (n : ℕ) (hn : n ≥ 3)
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = n) (h_sunny : ∀ l ∈ L, Sunny l)
  (L1 : Set (ℝ × ℝ)) (h_L1_in : L1 ∈ L)
  (σ : Equiv.Perm {i // i ∈ Finset.Icc (2:ℕ) n})
  (j : {i // i ∈ Finset.Icc (2:ℕ) n})
  (l : Set (ℝ × ℝ)) (hl : l ∈ L \\ {L1})
  (h_lj : ((1:ℝ), (j:ℝ)) ∈ l ∧ ((((σ j):ℕ):ℝ), (1:ℝ)) ∈ l) :
  let j_val := (j : ℕ);
  let sj_val := ((σ j) : ℕ);
  l = { v | v.1 * ((j_val : ℝ) - 1) + v.2 * ((sj_val : ℝ) - 1) = (j_val : ℝ) * (sj_val : ℝ) - 1 } := by
    -- By definition of $l$, we know that it passes through $(1, j)$ and $(\\sigma(j), 1)$.
    obtain ⟨a, b, c, hl_eq, ha, hb, hab⟩ := h_sunny l (Finset.mem_sdiff.mp hl).left;
    norm_num [ hl_eq ] at *;
    -- By solving the system of equations given by h_lj, we can express a and c in terms of b and the coordinates of j and σ(j).
    have h_sol : a = b * (1 - j.val) / (1 - (σ j).val) ∧ c = -b * (1 - j.val * (σ j).val) / (1 - (σ j).val) := by
      constructor <;> rw [ eq_div_iff ];
      · linarith;
      · exact sub_ne_zero_of_ne ( Ne.symm ( by norm_cast; linarith [ Finset.mem_Icc.mp ( σ j |>.2 ) ] ) );
      · cases lt_or_gt_of_ne ha <;> cases lt_or_gt_of_ne hb <;> nlinarith;
      · exact sub_ne_zero_of_ne ( Ne.symm ( by norm_cast; linarith [ Finset.mem_Icc.mp ( σ j |>.2 ) ] ) );
    -- Substitute the expressions for $a$ and $c$ into the equation $a*x + b*y + c = 0$ and simplify.
    have h_eq : ∀ x y : ℝ, a * x + b * y + c = 0 ↔ x * (j.val - 1) + y * ((σ j).val - 1) = j.val * (σ j).val - 1 := by
      intro x y; rw [ h_sol.1, h_sol.2 ];
      by_cases h : ( 1 - ( σ j : ℝ ) ) = 0 <;> simp_all ( config := { decide := Bool.true } ) [ field_simps ];
      constructor <;> intro <;> cases lt_or_gt_of_ne hb <;> nlinarith;
    exact?

/-
If a set of $n \\ge 3$ sunny lines covers $S_n$, then the line covering $(1,1)$ must be $y=x$.
-
-/
lemma lem_kn_point_22 (n : ℕ) (hn : n ≥ 3)
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = n) (h_sunny : ∀ l ∈ L, Sunny l)
  (h_cover : ∀ p ∈ s n, ∃ l ∈ L, p ∈ l)
  (L1 : Set (ℝ × ℝ)) (h_L1_in : L1 ∈ L) (h_L1_covers_1_1 : ((1:ℝ), (1:ℝ)) ∈ L1) :
  L1 = {v | v.1 = v.2} := by
    -- By Lemma~\\ref{lem:kn_setup}, the point $(2,2)$ must be covered by $L_1$.
    have h_cover_2_2 : ((2:ℝ), (2:ℝ)) ∈ L1 := by
      -- If $(2,2)$ is covered by some $l \\in L \\setminus \\{L1\\}$, then $(2,2)$ must be the unique point in $l$ that lies on the line $x=y$.
      by_contra h_contra
      obtain ⟨l, hlL, hl⟩ : ∃ l ∈ L \\ {L1}, ((2:ℝ), (2:ℝ)) ∈ l := by
        norm_num +zetaDelta at *;
        exact Exists.elim ( h_cover 2 2 ⟨ 2, 2, by norm_num, by norm_num, by linarith, by norm_num ⟩ ) fun l hl => ⟨ l, ⟨ hl.1, by rintro rfl; exact h_contra hl.2 ⟩, hl.2 ⟩;
      bound;
      -- Since $l$ is sunny, it must intersect the line $x=1$ at exactly one point and the line $y=1$ at exactly one point.
      obtain ⟨j, hj⟩ : ∃ j : Finset.Icc (2:ℕ) L.card, ((1:ℝ), (j:ℝ)) ∈ l := by
        have h_inter_x1 : ∀ j ∈ Finset.Icc (2:ℕ) L.card, ∃ l ∈ L \\ {L1}, ((1:ℝ), (j:ℝ)) ∈ l := by
          intro j hj;
          obtain ⟨ l, hlL, hl ⟩ := h_cover ( 1, j ) ⟨ 1, j, by norm_num, by linarith [ Finset.mem_Icc.mp hj ], by linarith [ Finset.mem_Icc.mp hj ], by norm_num ⟩;
          by_cases hlL1 : l = L1;
          · rcases h_sunny L1 h_L1_in with ⟨ a, b, c, rfl, ha, hb, hab ⟩;
            simp_all ( config := { decide := Bool.true } );
            -- Subtracting the second equation from the first gives b*(j-1) = 0. Since b ≠ 0, this implies j = 1, which contradicts hj.
            have h_contra : j = 1 := by
              exact_mod_cast ( mul_left_cancel₀ hb <| by linarith : ( j : ℝ ) = 1 );
            linarith;
          · exact ⟨ l, Finset.mem_sdiff.mpr ⟨ hlL, by aesop ⟩, hl ⟩;
        choose! f hf using h_inter_x1;
        have h_inter_x1 : Finset.image f (Finset.Icc (2:ℕ) L.card) = L \\ {L1} := by
          apply Finset.eq_of_subset_of_card_le;
          · exact Finset.image_subset_iff.mpr fun x hx => hf x hx |>.1;
          · rw [ Finset.card_image_of_injOn ];
            · rw [ Finset.card_sdiff ] <;> aesop;
            · intros x hx y hy; have := hf x hx; have := hf y hy; aesop;
              cases h_sunny _ ( hf x left_1 right_1 |>.1.1 ) ; aesop;
              have := hf y left_2 right_2; aesop;
              exact_mod_cast ( mul_left_cancel₀ left_4 <| by linarith : ( x : ℝ ) = y );
        replace h_inter_x1 := Finset.ext_iff.mp h_inter_x1 l; aesop;
      obtain ⟨i, hi⟩ : ∃ i : Finset.Icc (2:ℕ) L.card, (((i:ℝ), (1:ℝ)) ∈ l) := by
        have := lem_kn_setup L.card hn L ( by linarith ) h_sunny h_cover;
        obtain ⟨ L1, hL1_in, hL1_covers_1_1, hL1_cover ⟩ := this;
        -- By hypothesis hL1_cover, there exists a unique q in PtsY such that q is in l. Since PtsY is the image of the function that maps i to (i, 1) for i in 2 to L.card, there must be some i in this range where (i, 1) is in l.
        obtain ⟨q, hq⟩ : ∃ q ∈ Finset.image (fun i : ℕ => ((i : ℝ), (1 : ℝ))) (Finset.Icc (2:ℕ) L.card), q ∈ l := by
          -- By hypothesis hL1_cover, there exists a unique q in PtsY such that q is in l. Since PtsY is the image of the function that maps i to (i, 1) for i in 2 to L.card, there must be some i in this range where (i, 1) is in l. Hence, we can conclude that such a q exists.
          specialize hL1_cover l (by
          norm_num +zetaDelta at *;
          bound;
          rcases h_sunny l left with ⟨ a, b, c, rfl, ha, hb, hab ⟩;
          norm_num at *;
          exact hab ( by nlinarith [ show ( val : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp property ] ] ));
          exact hL1_cover.2.exists;
        aesop;
      rcases h_sunny l ( Finset.mem_sdiff.mp hlL |>.1 ) with ⟨ a, b, c, rfl, ha, hb, hab ⟩;
      rcases j with ⟨ _ | _ | _ | j, hj ⟩ <;> rcases i with ⟨ _ | _ | _ | i, hi ⟩ <;> norm_num at *;
      all_goals simp_all ( config := { decide := Bool.true } );
      · exact hab ( by linarith );
      · exact ha ( by nlinarith );
      · exact hab ( by nlinarith );
      · by_cases h : j = i;
        · exact hab ( by subst h; nlinarith );
        · exact h ( Nat.cast_injective ( by cases lt_or_gt_of_ne ha <;> cases lt_or_gt_of_ne hb <;> cases lt_or_gt_of_ne hab <;> nlinarith : ( j : ℝ ) = i ) );
    -- Since L1 is a sunny line, it must be of the form ax + by + c = 0 where a and b are non-zero and a ≠ b. Given that (1,1) and (2,2) are on this line, we can derive that a = -b.
    obtain ⟨a, b, c, hL1_eq, ha, hb, hab⟩ := h_sunny L1 h_L1_in;
    simp_all ( config := { decide := Bool.true } );
    norm_num [ show a = -b by linarith ] at *;
    exact Set.ext fun x => by aesop; cases lt_or_gt_of_ne ha <;> nlinarith;

/-
Suppose a set of 4 sunny lines covers $S_4$. Then one line is $y=x$, and the other three lines $L_2, L_3, L_4$ are determined by a derangement $\\sigma$ of $\\{2,3,4\\}$.
-
-/
lemma lem_kn_impossible_n4_setup
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = 4) (h_sunny : ∀ l ∈ L, Sunny l)
  (h_cover : ∀ p ∈ s 4, ∃ l ∈ L, p ∈ l) :
  ∃ (σ : Equiv.Perm {i // i ∈ Finset.Icc (2:ℕ) 4}) (h_derangement : ∀ j, σ j ≠ j),
    L = insert {v | v.1 = v.2}
      (Finset.image (fun j : {i // i ∈ Finset.Icc (2:ℕ) 4} =>
        { v | v.1 * ((j : ℝ) - 1) + v.2 * ((σ j : ℝ) - 1) = (j : ℝ) * (σ j : ℝ) - 1 }) Finset.univ) := by
          -- By Lemma~\\ref{lem:kn_point_22}, the line covering $(1,1)$ must be $y=x$.
          obtain ⟨L1, hL1_in, hL1_covers_1_1⟩ : ∃ L1 ∈ L, ((1:ℝ), (1:ℝ)) ∈ L1 ∧ L1 = {v : ℝ × ℝ | v.1 = v.2} := by
            have := lem_kn_point_22 4 ( by norm_num ) L h_card h_sunny h_cover;
            obtain ⟨ L1, hL1 ⟩ := h_cover ( 1, 1 ) ⟨ 1, 1, by norm_num ⟩;
            -- Apply the lemma to conclude that L1 must be the line y=x.
            apply Exists.intro L1 ⟨hL1.left, hL1.right, this L1 hL1.left hL1.right⟩;
          -- Apply lem_kn_permutation_setup to obtain the permutation σ.
          obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm {i : ℕ // i ∈ Finset.Icc (2:ℕ) 4}, ∀ j : {i : ℕ // i ∈ Finset.Icc (2:ℕ) 4}, ∃! l ∈ L \\ {L1}, ((1:ℝ), (j:ℝ)) ∈ l ∧ ((((σ j):ℕ):ℝ), (1:ℝ)) ∈ l := by
            apply lem_kn_permutation_setup;
            simp +zetaDelta at *;
            · exact h_card;
            · -- Apply the hypothesis that all lines in L are sunny.
              apply h_sunny;
            · assumption;
            · assumption;
            · exact hL1_covers_1_1.1;
          refine' ⟨ σ, _, _ ⟩;
          · -- By Lemma~\\ref{lem:kn_derangement}, σ is a derangement, so σ(j) ≠ j for all j.
            intros j
            apply lem_kn_derangement;
            all_goals tauto;
          · have h_lines : ∀ j : Finset.Icc (2:ℕ) 4, let l := Classical.choose (hσ j).exists; l ∈ L ∧ l ≠ L1 ∧ ((1:ℝ), (j:ℝ)) ∈ l ∧ (((σ j):ℝ), (1:ℝ)) ∈ l ∧ l = {v : ℝ × ℝ | v.1 * ((j : ℝ) - 1) + v.2 * ((σ j : ℝ) - 1) = (j : ℝ) * (σ j : ℝ) - 1} := by
              -- By Lemma~\\ref{lem:kn_line_equation}, the line $l$ must satisfy the equation $x(j-1) + y(\\sigma(j)-1) = j\\sigma(j)-1$.
              intros j
              set l := Classical.choose (hσ j).exists
              have hl : l ∈ L ∧ l ≠ L1 ∧ ((1:ℝ), (j:ℝ)) ∈ l ∧ (((σ j):ℝ), (1:ℝ)) ∈ l := by
                have := Classical.choose_spec ( hσ j |> ExistsUnique.exists ) ; aesop;
              have := lem_kn_line_equation 4 ( by norm_num ) L h_card h_sunny L1 hL1_in σ j l;
              simp +zetaDelta at *;
              exact ⟨ hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, this hl.1 hl.2.1 hl.2.2.1 hl.2.2.2 ⟩;
            -- Let's denote the lines in $L$ that are not $L1$ as $L2$, $L3$, and $L4$.
            have h_lines_non_L1 : Finset.image (fun j : Finset.Icc (2:ℕ) 4 => Classical.choose (hσ j).exists) Finset.univ = L \\ {L1} := by
              apply Finset.eq_of_subset_of_card_le;
              · simp_all ( config := { decide := Bool.true } ) [ Finset.image_subset_iff ];
                intro a b; specialize h_lines a b; aesop;
              · rw [ Finset.card_image_of_injective _ fun x y hxy => _ ];
                · rw [ Finset.card_sdiff ] <;> aesop;
                · bound;
                  have := Classical.choose_spec ( hσ ⟨ val, property ⟩ |> ExistsUnique.exists ) ; have := Classical.choose_spec ( hσ ⟨ val_1, property_1 ⟩ |> ExistsUnique.exists ) ; aesop;
                  cases h_sunny _ left ; aesop;
                  exact_mod_cast ( mul_left_cancel₀ left_4 <| by linarith : ( val : ℝ ) = val_1 );
            rw [ Finset.ext_iff ] at *;
            simp +zetaDelta at *;
            grind

/-
For $n=4$, it is impossible for a set of 4 sunny lines to cover $S_4$.
-
-/
lemma lem_kn_impossible_n4 :
  ¬ (∃ L : Finset (Set (ℝ × ℝ)), L.card = 4 ∧ (∀ l ∈ L, Sunny l) ∧ (∀ p ∈ s 4, ∃ l ∈ L, p ∈ l)) := by
    -- Apply the lemma that states any set of 4 sunny lines covering S_4 must be of the form described in Lemma~\\ref{lem:kn_impossible_n4_setup}.
    have h_config : ∀ L : Finset (Set (ℝ × ℝ)), L.card = 4 → (∀ l ∈ L, Sunny l) → (∀ p ∈ s 4, ∃ l ∈ L, p ∈ l) → ∃ σ : Equiv.Perm {i // i ∈ Finset.Icc (2:ℕ) 4}, (∀ j, σ j ≠ j) ∧ L = insert {v | v.1 = v.2} (Finset.image (fun j : {i // i ∈ Finset.Icc (2:ℕ) 4} => { v | v.1 * ((j : ℝ) - 1) + v.2 * ((σ j : ℝ) - 1) = (j : ℝ) * (σ j : ℝ) - 1 }) Finset.univ) := by
      bound;
      -- Apply the lemma that states any set of 4 sunny lines covering S_4 must be of the form described in Lemma~\\ref{lem:kn_impossible_n4_setup} to obtain the permutation σ.
      obtain ⟨σ, hσ⟩ := lem_kn_impossible_n4_setup L a a_1 a_2;
      use σ;
      exact ⟨ hσ.1, hσ.2 ⟩;
    intro h;
    -- Apply the lemma h_config to the set L from h to obtain the permutation σ and the structure of L.
    obtain ⟨L, hL_card, hL_sunny, hL_cover⟩ := h;
    obtain ⟨σ, hσ_derangement, hL_structure⟩ := h_config L hL_card hL_sunny hL_cover;
    subst hL_structure;
    fin_cases σ <;> simp ( config := { decide := Bool.true } ) at hσ_derangement hL_cover;
    · contrapose! hL_cover;
      refine' ⟨ 2, 3, _, _, _ ⟩ <;> norm_num;
      · exact ⟨ 2, 3, by norm_num ⟩;
      · rintro a x hx rfl; rcases hx with ⟨ hx₁, hx₂ ⟩ ; interval_cases x <;> norm_num [ Equiv.swap_apply_def ];
    · contrapose! hL_cover;
      refine' ⟨ 2, 3, _, _, _ ⟩ <;> norm_num;
      · exact ⟨ 2, 3, by norm_num ⟩;
      · rintro a x hx rfl; rcases hx with ⟨ hx₁, hx₂ ⟩ ; interval_cases x <;> norm_num [ Equiv.swap_apply_def ] ;

/-
Suppose for $n \\ge 5$ a set of $n$ sunny lines covers $S_n$. Then the permutation $\\sigma$ from Lemma~\\ref{lem:kn_permutation_setup} must satisfy $\\sigma(5)=3$ and $\\sigma(3)=5$.
-
-/
lemma lem_kn_impossible_n_ge_5_point_coverage (n : ℕ) (hn : n ≥ 5)
  (L : Finset (Set (ℝ × ℝ))) (h_card : L.card = n) (h_sunny : ∀ l ∈ L, Sunny l)
  (h_cover : ∀ p ∈ s n, ∃ l ∈ L, p ∈ l)
  (σ : Equiv.Perm {i // i ∈ Finset.Icc (2:ℕ) n})
  (h_sigma_prop : ∀ (j : {i // i ∈ Finset.Icc (2:ℕ) n}), ∃! l ∈ L \\ {{v | v.1 = v.2}}, ((1:ℝ), (j:ℝ)) ∈ l ∧ ((((σ j):ℕ):ℝ), (1:ℝ)) ∈ l) :
  (∃ h5 : 5 ∈ Finset.Icc (2:ℕ) n, σ (⟨5, h5⟩) = ⟨3, by
    -- Since $n \\geq 5$, we have $3 \\leq n$.
    have h3_le_n : 3 ≤ n := by
      linarith;
    exact Finset.mem_Icc.mpr ⟨ by norm_num, h3_le_n ⟩⟩) ∧
  (∃ h3 : 3 ∈ Finset.Icc (2:ℕ) n, σ (⟨3, h3⟩) = ⟨5, by
    norm_num; linarith⟩) := by
    constructor;
    · -- The point $(2,3) \\in S_n$ (since $2+3=5 \\le n+1$). It is not on $y=x$. By Lemma~\\ref{lem:kn_point_22}, $y=x$ is one of the lines. So $(2,3)$ must be on some $L_j$ for $j \\in \\{2,\\dots,n\\}$. From its equation in Lemma~\\ref{lem:kn_line_equation}, we have $2(j-1)+3(\\sigma(j)-1)=j\\sigma(j)-1$, which gives $(j-3)(\\sigma(j)-2)=2$. Since $j,\\sigma(j) \\in \\{2,\\dots,n\\}$ and $\\sigma(j) \\ne j$, the only solution is $j-3=2, \\sigma(j)-2=1$, which gives $j=5, \\sigma(5)=3$. This requires $n \\ge 5$.
      obtain ⟨l, hl⟩ : ∃ l ∈ L \\ { {v : ℝ × ℝ | v.2 = v.1} }, ((2 : ℝ), (3 : ℝ)) ∈ l := by
        -- Since $(2, 3) \\in s n$, by $h_cover$, there exists a line in $L$ that contains $(2, 3)$.
        obtain ⟨l, hl₁, hl₂⟩ : ∃ l ∈ L, ((2 : ℝ), (3 : ℝ)) ∈ l := by
          -- Since (2, 3) is in S_n, we can apply the coverage hypothesis h_cover to obtain the existence of a line in L that contains it.
          apply h_cover;
          exact ⟨ 2, 3, by norm_num, by norm_num, by linarith, by norm_num ⟩;
        norm_num +zetaDelta at *;
        exact ⟨ l, ⟨ hl₁, by rintro rfl; exact absurd hl₂ ( by norm_num ) ⟩, hl₂ ⟩;
      -- By Lemma~\\ref{lem:kn_line_equation}, the line $l$ must be of the form $x(j-1) + y(\\sigma(j)-1) = j\\sigma(j)-1$ for some $j \\in \\{2, \\dots, n\\}$.
      obtain ⟨j, hj⟩ : ∃ j : Finset.Icc 2 n, l = {v : ℝ × ℝ | v.1 * ((j : ℝ) - 1) + v.2 * ((σ j : ℝ) - 1) = (j : ℝ) * (σ j : ℝ) - 1} := by
        -- By Lemma~\\ref{lem:kn_line_equation}, the line $l$ must be of the form $x(j-1) + y(\\sigma(j)-1) = j\\sigma(j)-1$ for some $j \\in \\{2, \\dots, n\\}$. We can find such a $j$ using the properties of the lines in $L$.
        obtain ⟨j, hj⟩ : ∃ j : Finset.Icc 2 n, (1, (j : ℝ)) ∈ l ∧ (((σ j) : ℝ), (1 : ℝ)) ∈ l := by
          have h_line_eq : ∀ j : Finset.Icc 2 n, ∃ l ∈ L \\ { {v : ℝ × ℝ | v.2 = v.1} }, ((1 : ℝ), (j : ℝ)) ∈ l ∧ (((σ j : ℝ), (1 : ℝ)) ∈ l) := by
            -- By hypothesis h_sigma_prop, for each j in Finset.Icc 2 n, there exists a unique line in L \\ { {v | v.2 = v.1} } that contains (1, j) and (σ j, 1). Therefore, such a line exists for each j.
            intros j
            obtain ⟨l, hl⟩ := h_sigma_prop j
            use l;
            simp +zetaDelta at *;
            bound;
            simp +zetaDelta at *;
            norm_num [ left_2 ] at property;
          choose f hf using h_line_eq;
          have h_line_eq : Finset.image f Finset.univ = L \\ { {v : ℝ × ℝ | v.2 = v.1} } := by
            apply Finset.eq_of_subset_of_card_le;
            · exact Finset.image_subset_iff.mpr fun j _ => hf j |>.1;
            · rw [ Finset.card_image_of_injective ];
              · rw [ Finset.card_sdiff ] <;> aesop;
                have := lem_kn_point_22 L.card ( by linarith ) L;
                simp +zetaDelta at *;
                specialize this h_sunny h_cover;
                obtain ⟨ l, hl₁, hl₂ ⟩ := h_cover 1 1 ⟨ 1, 1, by norm_num, by norm_num, by linarith, by norm_num ⟩;
                specialize this l hl₁ hl₂ ; aesop;
                simpa only [ Set.ext_iff, eq_comm ] using hl₁;
              · intros j j' hj;
                have := hf j; have := hf j'; aesop;
                cases h_sunny _ left_1 ; aesop;
                exact_mod_cast ( mul_left_cancel₀ left_5 <| by linarith : ( val : ℝ ) = val_1 );
          replace h_line_eq := Finset.ext_iff.mp h_line_eq l; aesop;
          exact ⟨ w, hf w ⟨ left_1, right_2 ⟩ |>.2.1, ⟨ left_1, right_2 ⟩, hf w ⟨ left_1, right_2 ⟩ |>.2.2 ⟩;
        use j;
        -- By Lemma~\\ref{lem:kn_line_equation}, the line $l$ must satisfy the equation $x(j-1) + y(\\sigma(j)-1) = j\\sigma(j)-1$.
        apply lem_kn_line_equation;
        any_goals tauto;
        · grind;
        · have := lem_kn_point_22 n ( by linarith ) L h_card h_sunny h_cover;
          specialize h_cover ( 1, 1 ) ; aesop;
          specialize h_cover ⟨ 1, 1, by norm_num, by norm_num, by linarith, by norm_num ⟩ ; aesop;
          specialize this w left_2 right_3 ; aesop;
          convert left_2 using 1;
          exact Set.ext fun x => eq_comm;
      norm_num [ hj ] at hl;
      norm_cast at hl;
      -- From the equation $(j-3)(\\sigma(j)-2)=2$, we can solve for $j$ and $\\sigma(j)$.
      have h_solve : (j - 3 : ℤ) * (σ j - 2 : ℤ) = 2 := by
        norm_num [ Int.subNatNat_eq_coe ] at hl; linarith;
      have : ( j : ℤ ) - 3 ∣ 2 := h_solve ▸ dvd_mul_right _ _;
      have : ( j : ℤ ) - 3 ≤ 2 := Int.le_of_dvd ( by norm_num ) this; ( have : ( j : ℤ ) - 3 ≥ -2 := neg_le_of_abs_le ( Int.le_of_dvd ( by norm_num ) ( by rwa [ abs_dvd ] ) ) ; interval_cases _ : ( j : ℤ ) - 3 <;> simp_all ( config := { decide := Bool.true } ) );
      · linarith [ Finset.mem_Icc.mp ( σ j |>.2 ) ];
      · exact absurd h_solve ( by linarith [ Finset.mem_Icc.mp ( σ j |>.2 ) ] );
      · norm_num [ show ( j : ℕ ) = 4 by linarith ] at *;
        norm_num [ show ( σ j : ℕ ) = 4 by linarith ] at *;
        norm_num [ Int.subNatNat ] at hl;
        exact absurd ( h_sunny _ hl.1 ) ( by rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ ; rw [ Set.ext_iff ] at h₁ ; have h₅ := h₁ ( 0, 5 ) ; have h₆ := h₁ ( 5, 0 ) ; have h₇ := h₁ ( 1, 4 ) ; have h₈ := h₁ ( 4, 1 ) ; norm_num at h₅ h₆ h₇ h₈ ; cases lt_or_gt_of_ne h₂ <;> cases lt_or_gt_of_ne h₃ <;> cases lt_or_gt_of_ne h₄ <;> linarith );
      · simp_all ( config := { decide := Bool.true } ) [ sub_eq_iff_eq_add ]
        generalize_proofs at *;
        norm_cast at *;
        exact Subtype.eq ( by aesop );
    · -- By Lemma~\\ref{lem:kn_point_22}, $y=x$ is one of the lines. So $(3,2)$ must be on some $L_i$. This gives $3(i-1)+2(\\sigma(i)-1)=i\\sigma(i)-1$, which yields $(i-2)(\\sigma(i)-3)=2$.
      obtain ⟨i, hi⟩ : ∃ i : Finset.Icc (2 : ℕ) n, (3 : ℝ) * ((i : ℝ) - 1) + 2 * ((σ i : ℝ) - 1) = (i : ℝ) * (σ i : ℝ) - 1 := by
        field_simp;
        -- Since $(3, 2) \\in s_n$, there must be a line in $L$ that contains this point.
        obtain ⟨l, hl⟩ : ∃ l ∈ L, (3, 2) ∈ l := by
          exact h_cover _ ⟨ 3, 2, by norm_num, by norm_num, by linarith, by norm_num ⟩;
        by_cases hl_eq : l = {v : ℝ × ℝ | v.2 = v.1};
        · norm_num [ hl_eq ] at hl;
        · obtain ⟨j, hj⟩ : ∃ j : Finset.Icc (2 : ℕ) n, l ∈ L \\ { {v : ℝ × ℝ | v.2 = v.1} } ∧ (1, (j : ℝ)) ∈ l ∧ ((σ j : ℝ), 1) ∈ l := by
            have h_image : Finset.image (fun j : Finset.Icc (2 : ℕ) n => Classical.choose (h_sigma_prop j)) Finset.univ = L \\ { {v : ℝ × ℝ | v.2 = v.1} } := by
              apply Finset.eq_of_subset_of_card_le;
              · -- By definition of $h_sigma_prop$, each chosen line is in $L \\setminus \\{ {v | v.2 = v.1} \\}$.
                intros l hl
                obtain ⟨j, hj⟩ := Finset.mem_image.mp hl
                have h_line_in_L : Classical.choose (h_sigma_prop j) ∈ L \\ { {v : ℝ × ℝ | v.2 = v.1} } := by
                  bound;
                  have := Classical.choose_spec ( h_sigma_prop ⟨ val, property ⟩ );
                  simpa [ eq_comm ] using this.1.1;
                aesop;
              · rw [ Finset.card_image_of_injective ];
                · rw [ Finset.card_sdiff ] <;> aesop;
                  have := lem_kn_point_22 L.card ( by linarith ) L;
                  contrapose! this;
                  have := lem_kn_setup L.card ( by linarith ) L;
                  norm_num +zetaDelta at *;
                  -- Since $L1$ is in $L$ and $y=x$ is not in $L$, $L1$ cannot be $y=x$.
                  obtain ⟨L1, hL1_in, hL1_cover⟩ := this h_sunny h_cover;
                  have hL1_ne_yx : L1 ≠ {v : ℝ × ℝ | v.2 = v.1} := by
                    grind;
                  exact ⟨ h_sunny, h_cover, L1, hL1_in, hL1_cover.1, by simpa [ eq_comm ] using hL1_ne_yx ⟩;
                · intros j j' hj;
                  simp +zetaDelta at *;
                  have := Classical.choose_spec ( h_sigma_prop j ) |>.1; have := Classical.choose_spec ( h_sigma_prop j' ) |>.1; aesop;
                  cases h_sunny _ left_2 ; aesop;
                  exact_mod_cast ( mul_left_cancel₀ left_5 <| by linarith : ( val : ℝ ) = val_1 );
            -- Since $l \\in L \\setminus \\{ {v | v.2 = v.1} \\}$, by the definition of image, there exists a $j$ such that $l = \\text{Classical.choose}(\\text{h_sigma_prop}(j))$.
            obtain ⟨j, hj⟩ : ∃ j : Finset.Icc (2 : ℕ) n, l = Classical.choose (h_sigma_prop j) := by
              replace h_image := Finset.ext_iff.mp h_image l; aesop;
            -- By definition of choose, the chosen l for j is in L \\ { {v | v.2 = v.1} } and contains the required points.
            use j;
            have := Classical.choose_spec ( h_sigma_prop j );
            simp +zetaDelta at *;
            grind;
          use j.val;
          simp +zetaDelta at *;
          cases h_sunny l hl.1 ; aesop;
          · exact Finset.mem_Icc.mp property |>.1;
          · linarith [ Finset.mem_Icc.mp property ];
          · cases lt_or_gt_of_ne left_1 <;> cases lt_or_gt_of_ne left_3 <;> nlinarith;
      have h_sigma_3 : i.val = 3 ∧ (σ i).val = 5 := by
        norm_cast at hi;
        norm_num [ Int.subNatNat_eq_coe ] at hi;
        have h_i_sigma_i : (i.val - 2) * ((σ i).val - 3) = 2 := by
          rw [ Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib ];
          exact Nat.sub_eq_of_eq_add <| Nat.sub_eq_of_eq_add <| by nlinarith only [ hi, Nat.sub_add_cancel <| show 2 ≤ ( i : ℕ ) from Finset.mem_Icc.mp i.2 |>.1, Nat.sub_add_cancel <| show 2 ≤ ( σ i : ℕ ) from Finset.mem_Icc.mp ( σ i |>.2 ) |>.1 ] ;
        rcases x : ( i : ℕ ) - 2 with ( _ | _ | x ) <;> rcases y : ( σ i : ℕ ) - 3 with ( _ | _ | y ) <;> simp_all ( config := { decide := Bool.true } );
        · exact ⟨ by omega, by omega ⟩;
        · rw [ Nat.sub_eq_iff_eq_add ] at x y <;> aesop;
          · have := h_sigma_prop 4 ( by norm_num; linarith );
            obtain ⟨ l, hl₁, hl₂ ⟩ := this;
            obtain ⟨ a, b, c, rfl, ha, hb, hab ⟩ := h_sunny l hl₁.1.1;
            norm_num [ y ] at hl₁;
            exact hab ( by linarith );
          · omega;
          · exact Finset.mem_Icc.mp property |>.1;
        · nlinarith only [ h_i_sigma_i ];
      bound

/-
For $n \\ge 5$, it is impossible for a set of $n$ sunny lines to cover $S_n$.
-
-/
lemma lem_kn_impossible_n_ge_5 (n : ℕ) (hn : n ≥ 5) :
  ¬ (∃ L : Finset (Set (ℝ × ℝ)), L.card = n ∧ (∀ l ∈ L, Sunny l) ∧ (∀ p ∈ s n, ∃ l ∈ L, p ∈ l)) := by
    intro h;
    obtain ⟨ L, hL₁, hL₂, hL₃ ⟩ := h;
    -- Obtain the permutation σ from Lemma~\\ref{lem:kn_permutation_setup}.
    obtain ⟨σ, hσ_prop⟩ : ∃ σ : Equiv.Perm {i : ℕ // i ∈ Finset.Icc (2:ℕ) n}, (∀ j : {i : ℕ // i ∈ Finset.Icc (2:ℕ) n}, ∃! l ∈ L \\ { {v : ℝ × ℝ | v.1 = v.2} }, ((1:ℝ), (j:ℝ)) ∈ l ∧ ((((σ j):ℕ):ℝ), (1:ℝ)) ∈ l) := by
      -- By Lemma~\\ref{lem:kn_permutation_setup}, there exists a permutation σ of {2, ..., n} such that for each j, there's a unique line in L \\ { {v | v.1 = v.2} } covering (1, j) and (σ(j), 1).
      apply lem_kn_permutation_setup n (by linarith) L hL₁ hL₂ hL₃;
      · have := lem_kn_point_22 n ( by linarith ) L hL₁ hL₂ hL₃;
        obtain ⟨ l, hl₁, hl₂ ⟩ := hL₃ ( 1, 1 ) ⟨ 1, 1, by norm_num, by norm_num, by linarith, by norm_num ⟩;
        grind;
      · -- Since 1 equals 1, the point (1, 1) is in the set {v | v.1 = v.2}.
        simp;
    -- By Lemma~\\ref{lem:kn_impossible_n_ge_5_point_coverage}, we have σ(5)=3 and σ(3)=5.
    have hσ_5_3 : σ ⟨5, by
      -- Since $n \\geq 5$, we have $5 \\in [2, n]$.
      exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩ = ⟨3, by
      norm_num; linarith⟩ := by
      -- Apply the lemma lem_kn_impossible_n_ge_5_point_coverage to obtain σ(5) = 3.
      apply (lem_kn_impossible_n_ge_5_point_coverage n hn L hL₁ hL₂ hL₃ σ hσ_prop).left.choose_spec
    have hσ_3_5 : σ ⟨3, by
      norm_num; linarith⟩ = ⟨5, by
      norm_num; linarith⟩ := by
      have := lem_kn_impossible_n_ge_5_point_coverage n hn L hL₁ hL₂ hL₃ σ hσ_prop;
      aesop;
    -- Consider the point $(2,4) \\in S_n$ (since $2+4=6 \\le n+1$). It is not on $y=x$, so it must be on some $L_j$ for $j \\in \\{2, \\dots, n\\}$.
    have h_point_2_4 : ∃ j : { i : ℕ // i ∈ Finset.Icc 2 n }, ∃ l ∈ L \\ { {v : ℝ × ℝ | v.1 = v.2} }, ((2:ℝ), (4:ℝ)) ∈ l ∧ ((1:ℝ), (j:ℝ)) ∈ l ∧ ((((σ j):ℕ):ℝ), (1:ℝ)) ∈ l := by
      obtain ⟨ l, hl₁, hl₂ ⟩ := hL₃ ( 2, 4 ) ⟨ 2, 4, by norm_num, by norm_num, by linarith, by norm_num ⟩;
      obtain ⟨j, hj⟩ : ∃ j : { i : ℕ // i ∈ Finset.Icc 2 n }, l = Classical.choose (hσ_prop j) := by
        have h_cover : Finset.image (fun j : { i : ℕ // i ∈ Finset.Icc 2 n } => Classical.choose (hσ_prop j)) Finset.univ = L \\ { {v : ℝ × ℝ | v.1 = v.2} } := by
          apply Finset.eq_of_subset_of_card_le;
          · exact Finset.image_subset_iff.mpr fun j _ => Classical.choose_spec ( hσ_prop j ) |>.1.1;
          · rw [ Finset.card_image_of_injective ];
            · rw [ Finset.card_sdiff ] <;> aesop
              generalize_proofs at *;
              have := lem_kn_point_22 L.card ( by linarith ) L ( by aesop ) ( by aesop );
              -- By hypothesis hL₃, there exists a line L1 in L that contains (1,1).
              obtain ⟨L1, hL1₁, hL1₂⟩ : ∃ L1 ∈ L, ((1:ℝ), (1:ℝ)) ∈ L1 := by
                exact hL₃ 1 1 ⟨ 1, 1, by norm_num, by norm_num, by linarith, by norm_num ⟩;
              grind;
            · intro j j' hj;
              -- If the chosen lines for j and j' are the same, then the lines corresponding to j and j' must be the same. But since each line is uniquely determined by j, this can only happen if j = j'.
              have h_unique : ∀ j j' : { i : ℕ // i ∈ Finset.Icc 2 n }, Classical.choose (hσ_prop j) = Classical.choose (hσ_prop j') → j = j' := by
                intros j j' hj
                have h_unique : ∀ l ∈ L \\ { {v : ℝ × ℝ | v.1 = v.2} }, ∀ j j' : { i : ℕ // i ∈ Finset.Icc 2 n }, (1, (j : ℝ)) ∈ l → (1, (j' : ℝ)) ∈ l → j = j' := by
                  intros l hl j j' hj hj';
                  obtain ⟨ a, b, c, rfl, ha, hb, hab ⟩ := hL₂ l ( Finset.mem_sdiff.mp hl |>.1 );
                  simp +zetaDelta at *;
                  exact Subtype.eq ( Nat.cast_injective ( mul_left_cancel₀ hb <| by linarith : ( j : ℝ ) = j' ) );
                exact h_unique _ ( Classical.choose_spec ( hσ_prop j ) |>.1.1 ) _ _ ( Classical.choose_spec ( hσ_prop j ) |>.1.2.1 ) ( hj ▸ Classical.choose_spec ( hσ_prop j' ) |>.1.2.1 );
              exact h_unique j j' hj;
        -- Since $l$ is in $L \\setminus \\{ {v | v.1 = v.2} \\}$, by the definition of image, there must exist a $j$ such that $l$ is the chosen line for $j$.
        have hl_in_image : l ∈ Finset.image (fun j : { i : ℕ // i ∈ Finset.Icc 2 n } => Classical.choose (hσ_prop j)) Finset.univ := by
          replace h_cover := Finset.ext_iff.mp h_cover l; aesop;
        simpa [ eq_comm ] using Finset.mem_image.mp hl_in_image;
      use j;
      have := Classical.choose_spec ( hσ_prop j );
      exact ⟨ _, this.1.1, hj ▸ hl₂, this.1.2.1, this.1.2.2 ⟩;
    bound;
    -- Substitute the points into the line equation and derive a contradiction.
    have h_line_eq : 2 * (val - 1) + 4 * ((σ ⟨val, property⟩ : ℕ) - 1) = val * (σ ⟨val, property⟩ : ℕ) - 1 := by
      rcases hL₂ w ( Finset.mem_sdiff.mp left |>.1 ) with ⟨ a, b, c, rfl, ha, hb, hab ⟩;
      rcases val with ( _ | _ | val ) <;> norm_num at *;
      · norm_num at property;
      · norm_num at property;
      · rw [ ← @Nat.cast_inj ℝ ] ; norm_num
        generalize_proofs at *;
        rw [ Nat.cast_sub, Nat.cast_sub ] <;> push_cast;
        · cases lt_or_gt_of_ne ha <;> cases lt_or_gt_of_ne hb <;> nlinarith;
        · exact Nat.one_le_iff_ne_zero.mpr ( mul_ne_zero ( by linarith ) ( by linarith [ Finset.mem_Icc.mp ( σ ⟨ val + 1 + 1, property ⟩ |>.2 ) ] ) );
        · exact Finset.mem_Icc.mp ( σ ⟨ val + 1 + 1, property ⟩ |>.2 ) |>.1.trans' ( by norm_num );
    rcases val with ( _ | _ | val ) <;> norm_num at *;
    · norm_num at property;
    · norm_num at property;
    · rcases x : σ ⟨ val + 1 + 1, property ⟩ with ( _ | _ | _ | _ | _ | _ | k ) <;> simp_all +arith +decide;
      · have := σ.injective ( x.trans hσ_5_3.symm ) ; simp_all ( config := { decide := Bool.true } );
      · omega;
      · norm_num [ show val = 3 by linarith ] at *
        generalize_proofs at *;
        aesop;
      · rw [ eq_tsub_iff_add_eq_of_le ] at h_line_eq;
        · rcases k with ( _ | _ | k ) <;> repeat rcases val with ( _ | _ | val ) <;> try nlinarith only [ h_line_eq ] ;
        · nlinarith only

/-
It is impossible for a set of $n$ sunny lines to cover $S_n$ for any $n \\ge 4$.
-
-/
lemma lem_kn_impossible (n : ℕ) (hn : n ≥ 4) :
  ¬ (∃ L : Finset (Set (ℝ × ℝ)), L.card = n ∧ (∀ l ∈ L, Sunny l) ∧ (∀ p ∈ s n, ∃ l ∈ L, p ∈ l)) := by
    -- Split into two cases: n=4 and n≥5.
    by_cases hn4 : n = 4;
    · -- Since we have hn4 : n = 4, we can use this to rewrite the goal in terms of n=4.
      rw [hn4];
      exact?;
    · -- Apply the lemma lem_kn_impossible_n_ge_5 to the current case.
      apply lem_kn_impossible_n_ge_5 n (by
      exact hn.lt_of_ne' hn4)

/-
For any integer $n \\ge 3$, it is impossible to have a configuration with $k \\ge 4$ sunny lines.
-
-/
lemma lem_k_ge_4_impossible (n k : ℕ) (hn : n ≥ 3) (hk : k ≥ 4) :
  ¬ (∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = k) := by
      -- By induction on $n$, we can conclude that for all $n \\geq 3$, it is impossible to have a configuration with $k \\geq 4$ sunny lines.
      induction' n, Nat.succ_le.mpr hn using Nat.le_induction with n ih;
      · -- Apply the reduction lemma to the assumed configuration with k=4 for n=3.
        by_contra h_contra
        obtain ⟨lines, hlines⟩ := h_contra;
        simp +zetaDelta at *;
        linarith [ show ( Finset.filter Sunny lines ).card ≤ 3 by exact hlines.2.1 ▸ Finset.card_filter_le _ _ ];
      · -- Apply Lemma~\\ref{lem:reduction} to the assumed configuration for $n+1$.
        intro h
        obtain ⟨lines, hlines⟩ := h;
        by_cases h_non_sunny : ∃ l ∈ lines, ¬Sunny l ∧ (l = {v : ℝ × ℝ | v.1 = (1:ℝ)} ∨ l = {v : ℝ × ℝ | v.2 = (1:ℝ)} ∨ l = {v : ℝ × ℝ | v.1 + v.2 = (n + 2 : ℝ)});
        · -- Apply the reduction lemma to the current configuration, using the non-sunny line identified in h_non_sunny.
          obtain ⟨lines', hlines'⟩ := lem_reduction (n + 1) k (by linarith) ⟨lines, hlines.1, hlines.2.1, hlines.2.2.1, hlines.2.2.2, by
            bound;
            · exact Or.inl left_2;
            · exact Or.inr <| Or.inl left_2;
            · exact Or.inr <| Or.inr <| by convert left_2 using 1; push_cast; ring;⟩;
          exact ‹n ≥ 3 → ¬∃ lines : Finset ( Set ( ℝ × ℝ ) ), ( ∀ line ∈ lines, ∃ a b c : ℝ, ¬ ( a = 0 ∧ b = 0 ) ∧ line = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 } ) ∧ lines.card = n ∧ ( ∀ p ∈ s n, ∃ l ∈ lines, p ∈ l ) ∧ ( Finset.filter Sunny lines ).card = k› ih ⟨ lines', hlines'.1, hlines'.2.1, hlines'.2.2.1, hlines'.2.2.2 ⟩;
        · by_cases h_boundary : {v : ℝ × ℝ | v.1 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.2 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.1 + v.2 = (n + 2 : ℝ)} ∈ lines;
          · norm_num +zetaDelta at *;
            rcases h_boundary with ( h | h | h );
            · specialize h_non_sunny _ h;
              norm_num at h_non_sunny;
              obtain ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ := h_non_sunny;
              norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
              exact h₃ ( by linarith [ h₁.1 1 0 rfl, h₁.1 1 1 rfl ] );
            · have h_non_sunny_y1 : ¬Sunny {v : ℝ × ℝ | v.2 = 1} := by
                rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
                norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
                exact h₂ ( by linarith [ h₁.1 0, h₁.1 1 ] );
              exact h_non_sunny _ h h_non_sunny_y1 |>.2.1 rfl;
            · specialize h_non_sunny _ h;
              norm_num +zetaDelta at *;
              obtain ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ := h_non_sunny;
              norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
              exact h₄ ( by linarith [ h₁.1 ( n + 2 ) 0 ( by ring ), h₁.1 ( n + 1 ) 1 ( by ring ), h₁.1 ( n ) 2 ( by ring ) ] );
          · have h_all_sunny : ∀ l ∈ lines, Sunny l := by
              intros l hl;
              contrapose! h_non_sunny;
              use l;
              bound;
              have := lem_boundary_lines_implication ( n + 1 ) ( by linarith ) lines;
              norm_num +zetaDelta at *;
              exact absurd ( this left_1 left left_2 h_boundary.1 h_boundary.2.1 ( mod_cast h_boundary.2.2 ) l hl ) h_non_sunny;
            have := lem_kn_impossible ( n + 1 ) ( by linarith );
            exact this ⟨ lines, hlines.2.1, h_all_sunny, hlines.2.2.1 ⟩

/-
For $n=3$, it is impossible to have a configuration with $k=2$ sunny lines.
-
-/
lemma lem_k2_impossible_n3 :
  ¬ (∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = 3 ∧
    (∀ p ∈ s 3, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 2) := by
      -- Assume that there are two sunny lines, L1 and L2, and a third line, L3, that covers the remaining points.
      intro h
      obtain ⟨lines, hlines⟩ := h
      obtain ⟨L1, L2, L3, hL1, hL2, hL3, h_cover⟩ : ∃ L1 L2 L3 : Set (ℝ × ℝ), L1 ∈ lines ∧ L2 ∈ lines ∧ L3 ∈ lines ∧ L1 ≠ L2 ∧ L1 ≠ L3 ∧ L2 ≠ L3 ∧ Sunny L1 ∧ Sunny L2 ∧ ¬Sunny L3 ∧ (∀ p ∈ s 3, p ∈ L1 ∨ p ∈ L2 ∨ p ∈ L3) := by
        -- Since there are exactly 2 sunny lines, there must be exactly 1 non-sunny line.
        obtain ⟨L3, hL3⟩ : ∃ L3 : Set (ℝ × ℝ), L3 ∈ lines ∧ ¬Sunny L3 := by
          contrapose! hlines;
          rw [ Finset.filter_true_of_mem hlines ] ; aesop;
        -- Since there are exactly 2 sunny lines, we can obtain them from the filter.
        obtain ⟨L1, L2, hL1, hL2, hL_distinct⟩ : ∃ L1 L2 : Set (ℝ × ℝ), L1 ∈ lines ∧ L2 ∈ lines ∧ L1 ≠ L2 ∧ Sunny L1 ∧ Sunny L2 ∧ L1 ≠ L3 ∧ L2 ≠ L3 := by
          obtain ⟨ L1, hL1, L2, hL2, hne ⟩ := Finset.one_lt_card.1 ( by linarith : 1 < Finset.card ( Finset.filter Sunny lines ) ) ; use L1, L2; aesop;
        have := Finset.eq_of_subset_of_card_le ( show { L1, L2, L3 } ⊆ lines from by intros x hx; aesop ) ; aesop;
      -- Since $L3$ is not sunny, it must be of the form $x=c$, $y=c$, or $x+y=c$ for some constant $c$.
      obtain (hL3_x | hL3_y | hL3_xy) : (∃ c : ℝ, L3 = {v : ℝ × ℝ | v.1 = c}) ∨ (∃ c : ℝ, L3 = {v : ℝ × ℝ | v.2 = c}) ∨ (∃ c : ℝ, L3 = {v : ℝ × ℝ | v.1 + v.2 = c}) := by
        -- Since $L3$ is not sunny, by the lemma lem_non_sunny_form, it must be of the form $x=c$, $y=c$, or $x+y=c$.
        apply (lem_non_sunny_form L3 (by
        exact hlines.1 L3 hL3)).mp;
        exact ⟨ hlines.1 L3 hL3, h_cover.2.2.2.2.2.1 ⟩;
      · -- If $L3$ is of the form $x = c$, then it can only cover points where the $x$-coordinate is $c$. However, since $c$ is a constant, it cannot cover all three points in $s 3$.
        obtain ⟨c, hc⟩ := hL3_x
        have h_cover_x : ∀ p ∈ ({(1,1), (1,2), (1,3), (2,1), (2,2), (3,1)} : Set (ℝ × ℝ)), p ∈ L1 ∨ p ∈ L2 ∨ p ∈ L3 := by
          bound;
          exact right_1 _ ⟨ Nat.floor fst, Nat.floor snd, by rcases a with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num, by rcases a with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num, by rcases a with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num, by rcases a with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num ⟩;
        rcases h_cover.2.2.2.1 with ⟨ a, b, c, rfl, ha, hb, hab ⟩ ; rcases h_cover.2.2.2.2.1 with ⟨ d, e, f, rfl, hd, he, hde ⟩ ; norm_num [ hc ] at *;
        rcases h_cover_x.1 with h | h | rfl;
        · simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
          bound;
          any_goals contrapose! hde; linarith;
          exact hd ( by linarith );
        · simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
          bound;
          any_goals contrapose! hab; linarith;
          exact ha ( by linarith );
        · norm_num at *;
          bound;
      · obtain ⟨ c, rfl ⟩ := hL3_y;
        -- Let's consider the points $(1,1)$, $(1,2)$, $(1,3)$, $(2,1)$, $(2,2)$, $(3,1)$ and see which ones are covered by the lines $L1$ and $L2$.
        have h_points : ∀ p ∈ ({(1,1), (1,2), (1,3), (2,1), (2,2), (3,1)} : Set (ℝ × ℝ)), p ∈ L1 ∨ p ∈ L2 ∨ p ∈ {v : ℝ × ℝ | v.2 = c} := by
          exact fun p hp => h_cover.2.2.2.2.2.2 p <| by rcases hp with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> [ exact ⟨ 1, 1, by norm_num ⟩ ; exact ⟨ 1, 2, by norm_num ⟩ ; exact ⟨ 1, 3, by norm_num ⟩ ; exact ⟨ 2, 1, by norm_num ⟩ ; exact ⟨ 2, 2, by norm_num ⟩ ; exact ⟨ 3, 1, by norm_num ⟩ ] ;
        rcases h_cover.2.2.2.1 with ⟨ a, b, c, rfl, ha, hb, hab ⟩ ; rcases h_cover.2.2.2.2.1 with ⟨ d, e, f, rfl, hd, he, hde ⟩ ; norm_num at *;
        rcases h_points.1 with h | h | rfl;
        · simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
          bound;
          any_goals contrapose! hde; linarith;
          grind +ring;
        · simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
          bound;
          any_goals contrapose! hab; linarith;
          grind +ring;
        · norm_num at *;
          bound;
      · obtain ⟨ c, rfl ⟩ := hL3_xy;
        -- Let's consider the points in $s_3$ and see which ones can be covered by the sunny lines $L1$ and $L2$.
        have h_points : ∀ p ∈ ({(1,1), (1,2), (1,3), (2,1), (2,2), (3,1)} : Set (ℝ × ℝ)), p ∈ L1 ∨ p ∈ L2 ∨ p ∈ {v : ℝ × ℝ | v.1 + v.2 = c} := by
          exact fun p hp => h_cover.2.2.2.2.2.2 p <| by rcases hp with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> [ exact ⟨ 1, 1, by norm_num ⟩ ; exact ⟨ 1, 2, by norm_num ⟩ ; exact ⟨ 1, 3, by norm_num ⟩ ; exact ⟨ 2, 1, by norm_num ⟩ ; exact ⟨ 2, 2, by norm_num ⟩ ; exact ⟨ 3, 1, by norm_num ⟩ ] ;
        rcases h_cover.2.2.2.1 with ⟨ a, b, c, rfl, ha, hb, hab ⟩ ; rcases h_cover.2.2.2.2.1 with ⟨ d, e, f, rfl, hd, he, hde ⟩ ; norm_num at *;
        rcases h_points.1 with h | h | rfl;
        · simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
          bound;
          all_goals contrapose! hde; linarith;
        · simp_all ( config := { decide := Bool.true } ) [ ← eq_sub_iff_add_eq ];
          bound;
          all_goals contrapose! hab; linarith;
        · norm_num at *;
          bound;
          any_goals contrapose! hde; linarith;
          all_goals contrapose! hab; linarith

/-
For any integer $n \\ge 3$, it is impossible to have a configuration with $k=2$ sunny lines.
-
-/
lemma lem_k2_impossible (n : ℕ) (hn : n ≥ 3) :
  ¬ (∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 2) := by
      -- Assume for contradiction that there exists a configuration with $k=2$ sunny lines.
      by_contra h_contra;
      -- By Lemma~\\ref{lem:reduction}, if there exists a configuration with $k=2$ for $n \\geq 4$, then there exists a configuration with $k=2$ for $n-1$.
      have h_reduction : ∀ n ≥ 4, (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = n ∧ (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) → (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = n - 1 ∧ (∀ p ∈ s (n - 1), ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) := by
        -- Apply Lemma~\\ref{lem:reduction} to the given configuration for $n \\geq 4$.
        intros n hn h_config
        obtain ⟨lines, hlines⟩ := h_config;
        by_cases h_boundary : {v : ℝ × ℝ | v.1 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.2 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.1 + v.2 = (n + 1 : ℝ)} ∈ lines;
        · have := lem_reduction n 2 ( by linarith );
          exact this ⟨ lines, hlines.1, hlines.2.1, hlines.2.2.1, hlines.2.2.2, h_boundary ⟩;
        · have := lem_boundary_lines_implication n ( by linarith ) lines;
          simp_all ( config := { decide := Bool.true } );
          exact absurd hlines.2.2.2 ( by rw [ Finset.filter_true_of_mem this ] ; linarith );
      -- By repeatedly applying the reduction lemma, we can reduce the problem to the case where $n=3$.
      have h_reduction_to_3 : ∀ n ≥ 4, (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = n ∧ (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) → (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = 3 ∧ (∀ p ∈ s 3, ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) := by
        intro n hn h;
        induction' hn with n hn ih;
        · exact h_reduction 4 ( by norm_num ) h;
        · exact ih ( h_reduction _ ( Nat.le_succ_of_le hn ) h );
      by_cases hn4 : n ≥ 4;
      · exact lem_k2_impossible_n3 ( h_reduction_to_3 n hn4 h_contra );
      · exact lem_k2_impossible_n3 ( by interval_cases n ; exact h_contra )

/-
A line in the plane is called sunny if it is not parallel to any of the $x$-axis, the $y$-axis, and the line $x+y=0$.
Let $n \\geqslant 3$ be a given integer. Determine all nonnegative integers $k$ such that there exist $n$ distinct lines in the plane satisfying both of the following:
- for all positive integers $a$ and $b$ with $a+b \\leqslant n+1$, the point $(a, b)$ is on at least one of the lines; and
- exactly $k$ of the $n$ lines are sunny.
-/
theorem main_theorem
  (n : ℕ)
  (hn : n ≥ 3) :
  {0, 1, 3} = { k | ∃ lines : Finset (Set (ℝ × ℝ)),
      (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 }) ∧
      lines.card = n ∧
      (∀ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 → ∃ (l : Set (ℝ × ℝ)), l ∈ lines ∧ ((a : ℝ), (b : ℝ)) ∈ l) ∧
      ((lines.filter (fun l => ∃ a b c, l = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 } ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)).card = k) } := by
        ext k;
        -- For the forward direction, if k is 0, 1, or 3, then by the lemmas we have, there exists such a set of lines.
        apply Iff.intro;
        · simp +zetaDelta at *;
          -- For each case, we can apply the corresponding lemma to construct the required set of lines.
          intro hk
          cases' hk with hk0 hk1 hk3;
          · convert lem_k0_possible n hn;
            · aesop;
            · -- By definition of $s$, if $(a, b) \\in s n$, then there exist $a$ and $b$ such that $0 < a$, $0 < b$, $a + b \\leq n + 1$, and $(a, b) = ((a : ℝ), (b : ℝ))$.
              unfold s; aesop;
            · -- By definition of Sunny, if there exist a, b, c such that the line is defined by a*x + b*y + c = 0 and a, b are non-zero and not equal, then the line is sunny.
              unfold Sunny; aesop;
          · bound;
            · convert lem_k1_possible n hn;
              · bound;
              · unfold s; aesop;
              · unfold Sunny; aesop;
            · convert lem_k3_possible n hn;
              · bound;
              · unfold s; aesop;
              · unfold Sunny; aesop;
        · -- By combining the results from the lemmas, we can conclude that k must be 0, 1, or 3.
          intros hk
          obtain ⟨lines, hlines⟩ := hk;
          -- By Lemma~\\ref{lem:k_ge_4_impossible}, $k \\leq 3$.
          have hk_le_3 : k ≤ 3 := by
            have := lem_k_ge_4_impossible n k hn;
            contrapose! this;
            simp +zetaDelta at *;
            exact ⟨ this, lines, hlines.1, hlines.2.1, fun a b hab => by rcases hab with ⟨ a', b', ha', hb', hab', rfl, rfl ⟩ ; exact hlines.2.2.1 a' b' ha' hb' hab', by convert hlines.2.2.2 using 2; ext; unfold Sunny; aesop ⟩;
          interval_cases k <;> norm_num;
          -- By Lemma~\\ref{lem:k2_impossible}, there cannot be a configuration with $k=2$.
          apply lem_k2_impossible n hn;
          use lines;
          unfold Sunny; aesop;
          cases a_1 ; aesop

#print axioms main_theorem
`,A=`/-
Let $\\mathbb{N}$ denote the set of positive integers.
A function $f\\colon\\mathbb{N} \\to \\mathbb{N}$ is said to be \\emph{bonza} if
$$ f(a) \\ \\ \\text{divides} \\ \\ b^a - f(b)^{f(a)} $$
for all positive integers $a$ and $b$.
Determine the smallest real constant $c$ such that
$f(n)\\leqslant cn$ for all bonza functions $f$ and all positive integers $n$.
Answer: 4
-/

import HarmonicLean.Imports

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace IMO2025P3

/-
A function $f\\colon\\mathbb{N} \\to \\mathbb{N}$ is said to be \\emph{bonza} if
$$f(a) \\text{ divides } b^a - f(b)^{f(a)}$$
for all positive integers $a$ and $b$.
-/
def isBonza (f : ℕ+ → ℕ+) : Prop :=
  ∀ a b : ℕ+, (b : ℕ) ^ (a : ℕ) ≡ (f b : ℕ) ^ (f a : ℕ) [MOD f a]

/-
For a bonza function $f$, let $S$ be the set of prime numbers $p$ for which $f(p) > 1$.
-/
def S (f : ℕ+ → ℕ+) : Set ℕ+ :=
  {p | Nat.Prime (p : ℕ) ∧ f p > 1}

/-
The function $f: \\mathbb{N} \\to \\mathbb{N}$ defined by
$$f(n) = \\begin{cases}
1 & \\text{if } n \\text{ is odd} \\\\
4 & \\text{if } n \\equiv 2 \\pmod{4} \\\\
16 & \\text{if } n \\equiv 0 \\pmod{4}
\\end{cases}$$
is a bonza function.
-/
def f_construction : ℕ+ → ℕ+ := fun n ↦
  if Odd (n : ℕ) then
    1
  else if (n : ℕ) % 4 = 2 then
    4
  else
    16

/-
If $f$ is a bonza function, then $f(n) \\mid n^n$ for all $n \\in \\mathbb{N}$.
-/
lemma f_n_divides_n_n (f : ℕ+ → ℕ+) (h : isBonza f) (n : ℕ+) : (f n : ℕ) ∣ (n : ℕ) ^ (n : ℕ) := by
  have := h n n;
  exact Nat.dvd_of_mod_eq_zero ( this.symm ▸ Nat.modEq_zero_iff_dvd.mpr ( dvd_pow_self _ ( PNat.ne_zero _ ) ) )

/-
If $f$ is a bonza function and $p$ is a prime number, then $f(p)$ must be a power of $p$.
-/
lemma prime_power_form (f : ℕ+ → ℕ+) (h : isBonza f) (p : ℕ+) (hp : Nat.Prime (p : ℕ)) :
  ∃ k : ℕ, (f p : ℕ) = (p : ℕ) ^ k := by
  have := h p p;
  -- From Lemma 2, we know that f(p) divides p^p.
  have h_div : (f p : ℕ) ∣ (p : ℕ) ^ (p : ℕ) := by
    exact Nat.dvd_of_mod_eq_zero ( this.symm ▸ Nat.modEq_zero_iff_dvd.mpr ( dvd_pow_self _ ( PNat.ne_zero _ ) ) );
  rw [ Nat.dvd_prime_pow ] at h_div <;> aesop

lemma construction_bonza : isBonza f_construction := by
  -- By definition of $f_construction$, we know that for any $a$, $f(a)$ is either $1$, $4$, or $16$.
  have h_cases : ∀ a : ℕ+, f_construction a = 1 ∨ f_construction a = 4 ∨ f_construction a = 16 := by
    aesop;
    unfold f_construction;
    split_ifs <;> simp ( config := { decide := Bool.true } );
  -- Now consider the three cases for $f(a)$ and show that $f(a) \\mid b^a - f(b)^{f(a)}$ for all $a$ and $b$.
  intros a b
  rcases h_cases a with ha | ha | ha;
  · -- Since $f_construction a = 1$, the congruence $b^a \\equiv f_construction b \\pmod{1}$ holds trivially because any integer is congruent to any other integer modulo 1.
    simp [ha, Nat.ModEq];
    rw [ Nat.mod_one, Nat.mod_one ];
  · rcases h_cases b with ( hb | hb | hb ) <;> simp_all ( config := { decide := Bool.true } );
    · unfold f_construction at * ; aesop;
      · rw [ Nat.odd_iff ] at hb; omega;
      · -- Since $b$ is odd, we can write $b = 2k + 1$ for some integer $k$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, b = 2 * k + 1 := hb;
        norm_num [ Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ];
        rw [ ← Nat.mod_add_div a 4, h_2 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ; have := Nat.mod_lt k zero_lt_four ; interval_cases k % 4 <;> norm_num;
    · rcases Nat.even_or_odd' ( b : ℕ ) with ⟨ c, d | d ⟩ <;> norm_num [ Nat.ModEq, Nat.pow_mod, Nat.mul_mod, d ];
      · rcases a with ( _ | _ | a ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
        · contradiction;
        · cases ha;
        · have := Nat.mod_lt c zero_lt_four; interval_cases c % 4 <;> norm_num [ Nat.pow_mod ] ;
      · unfold f_construction at hb; aesop;
    · -- Since $f(b) = 16$, we know that $b$ is divisible by $4$. Therefore, $b^{a}$ is divisible by $4^2 = 16$, making $b^{a} \\equiv 0 \\pmod{4}$.
      have hb_div : 4 ∣ (b : ℕ) := by
        unfold f_construction at hb; aesop;
        exact Nat.dvd_of_mod_eq_zero ( by rw [ Nat.even_iff ] at h; omega );
      norm_num [ Nat.ModEq, Nat.pow_mod, Nat.mod_eq_zero_of_dvd hb_div ];
  · -- Since $a$ is a multiple of 4, we can write $a = 4k$ for some $k \\in \\mathbb{N}$.
    obtain ⟨k, rfl⟩ : ∃ k : ℕ+, a = 4 * k := by
      -- Since $a$ is even and $f_construction a = 16$, it follows that $a$ must be a multiple of 4.
      have ha_mod : (a : ℕ) % 4 = 0 := by
        unfold f_construction at ha ; aesop;
        rw [ Nat.even_iff ] at h; omega;
      exact PNat.dvd_iff.mpr ( Nat.dvd_of_mod_eq_zero ha_mod );
    cases h_cases b <;> aesop;
    · -- Since $b$ is odd, we can write $b = 2m + 1$ for some $m \\in \\mathbb{N}$.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, b = 2 * m + 1 := by
        unfold f_construction at h; aesop;
      norm_num [ Nat.ModEq, Nat.pow_mul, Nat.pow_mod, hm ];
      norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ; have := Nat.mod_lt m ( by decide : 0 < 16 ) ; interval_cases m % 16 <;> norm_num;
    · unfold f_construction at * ; aesop;
      norm_num [ Nat.ModEq, Nat.pow_mul, Nat.pow_mod, h_2 ];
      rw [ ← Nat.mod_mod_of_dvd _ ( by decide : 4 ∣ 16 ) ] at h_2; have := Nat.mod_lt ( b : ℕ ) ( by decide : 0 < 16 ) ; interval_cases ( b : ℕ ) % 16 <;> norm_num at h_2 ⊢;
    · -- Since $b$ is a multiple of 4, we can write $b = 4m$ for some $m \\in \\mathbb{N}$.
      obtain ⟨m, rfl⟩ : ∃ m : ℕ+, b = 4 * m := by
        unfold f_construction at h_2;
        aesop;
        exact PNat.dvd_iff.mpr ( show 4 ∣ ( b : ℕ ) from Nat.dvd_of_mod_eq_zero ( by obtain ⟨ m, hm ⟩ := h; omega ) );
      norm_num [ Nat.ModEq, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ];
      have := Nat.mod_lt ( m : ℕ ) ( by decide : 0 < 16 ) ; interval_cases ( m : ℕ ) % 16 <;> norm_num [ Nat.pow_mod ] ;

/-
If $f$ is a bonza function for which $S=\\{2\\}$, then for any odd integer $n>1$, $f(n)=1$.
-/
lemma odd_n_gives_f_n_one (f : ℕ+ → ℕ+) (h : isBonza f) (hS : S f = {(2 : ℕ+)}) (n : ℕ+)
    (hn_odd : Odd (n : ℕ)) (hn_gt_one : n > 1) :
  f n = 1 := by
  -- Since $n$ is odd and greater than 1, all its prime factors are odd primes. For any odd prime $p$, we have $f(p) = 1$ because $S(f) = \\{2\\}$.
  have h_prime_factors : ∀ p : ℕ+, Nat.Prime p → p ∣ n → f p = 1 := by
    rw [ Set.eq_singleton_iff_unique_mem ] at hS;
    -- Since $p$ is a prime divisor of $n$ and $n$ is odd, $p$ cannot be $2$. Therefore, $p$ is not in $S(f)$, which implies $f(p) \\leq 1$.
    intros p hp_prime hp_div
    have hp_not_in_S : p ∉ S f := by
      intros H; specialize hS; have := hS.2 p H; simp_all ( config := { decide := Bool.true } ) [ PNat.dvd_iff, Nat.prime_dvd_prime_iff_eq ] ;
      -- Since $n$ is odd, $2$ cannot divide $n$, leading to a contradiction.
      exact absurd hp_div (by simpa [ ← even_iff_two_dvd ] using hn_odd);
    unfold S at *; aesop;
  -- Since $f(n)$ divides $p^n - 1$ for any prime factor $p$ of $n$, and $p$ divides $n$, it follows that $f(n)$ is coprime with $p$.
  have h_coprime : ∀ p : ℕ+, Nat.Prime p → p ∣ n → Nat.gcd (f n) p = 1 := by
    intros p hp_prime hp_div
    have h_div : (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - 1 := by
      have := h n p;
      rw [ ← Nat.modEq_zero_iff_dvd ] ; have := this.symm.dvd; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.eq_iff_modEq_nat ] ;
    refine' Nat.Coprime.coprime_dvd_left h_div _;
    refine' Nat.Coprime.symm ( hp_prime.coprime_iff_not_dvd.mpr _ );
    haveI := Fact.mk hp_prime; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub ( Nat.one_le_pow _ _ hp_prime.pos ) ] ;
  -- Since $f(n)$ is coprime with all prime factors of $n$, it must be coprime with $n$ itself.
  have h_coprime_n : Nat.gcd (f n) n = 1 := by
    refine' Nat.Coprime.symm <| Nat.coprime_of_dvd <| _;
    exact fun k hk hk' hk'' => hk.not_dvd_one <| h_coprime ⟨ k, hk.pos ⟩ hk ( PNat.dvd_iff.mpr hk' ) ▸ Nat.dvd_gcd hk'' ( dvd_refl _ );
  -- Since $f(n)$ divides $n^n$ and $f(n)$ is coprime with $n$, it follows that $f(n)$ must divide $1$.
  have h_div_one : (f n : ℕ) ∣ (n : ℕ) ^ (n : ℕ) ∧ Nat.gcd (f n) n = 1 → (f n : ℕ) ∣ 1 := by
    exact fun h => by have := Nat.dvd_gcd ( dvd_refl _ ) h.1; simp_all ( config := { decide := Bool.true } ) [ Nat.Coprime, Nat.Coprime.pow_right ] ;
  exact PNat.eq ( Nat.eq_one_of_dvd_one <| h_div_one ⟨ f_n_divides_n_n f h n, h_coprime_n ⟩ )

/-
If $f$ is a bonza function and $p \\in S$ (per Definition~\\ref{def:S}), then $f(b) \\equiv b \\pmod{p}$ for all $b \\in \\mathbb{N}$.
-/
lemma fermat_congruence (f : ℕ+ → ℕ+) (h : isBonza f) (p : ℕ+) (hp : p ∈ S f) (b : ℕ+) :
  (f b : ℕ) ≡ (b : ℕ) [MOD p] := by
  -- Since $p$ is a prime and $f(p) > 1$, we know that $f(p)$ is a power of $p$. Let $f(p) = p^k$ for some $k \\geq 1$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (f p : ℕ) = (p : ℕ) ^ k := by
    -- Apply the lemma that states $f(p)$ must be a power of $p$ for a bonza function $f$ and a prime $p$.
    apply prime_power_form f h p hp.left;
  -- Applying the definition of $P(a,b)$ with $a=p$, we get $b^p \\equiv f(b)^{f(p)} \\pmod{p}$.
  have hb_mod_p : (b : ℕ) ^ (p : ℕ) ≡ (f b : ℕ) ^ (f p : ℕ) [MOD p] := by
    have hb_mod_p : (b : ℕ) ^ (p : ℕ) ≡ (f b : ℕ) ^ (f p : ℕ) [MOD f p] := by
      exact?;
    -- Since $p$ divides $f(p)$, the congruence modulo $f(p)$ implies the congruence modulo $p$.
    have h_div : (p : ℕ) ∣ (f p : ℕ) := by
      rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ pow_succ' ];
      have := hp.2; aesop;
    exact hb_mod_p.of_dvd h_div;
  haveI := Fact.mk hp.left; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.eq_iff_modEq_nat ] ;

/-
If $f$ is a bonza function for which $S=\\{2\\}$, and $n$ is an even integer, then $f(n)$ is a power of 2.
-/
lemma even_n_power_of_two (f : ℕ+ → ℕ+) (h : isBonza f) (hS : S f = {(2 : ℕ+)}) (n : ℕ+)
    (hn_even : Even (n : ℕ)) :
  ∃ k : ℕ, (f n : ℕ) = 2 ^ k := by
  have h_prime_factors : ∀ p : ℕ+, Nat.Prime p → p ≠ 2 → ¬ (p ∣ f n) := by
    -- If $p$ divides $f(n)$, then by the definition of $S(f)$, $p$ must be in $S(f)$.
    have h_prime_in_S : ∀ p : ℕ+, Nat.Prime p → p ∣ f n → p ∈ S f := by
      -- If $p$ divides $f(n)$, then by the definition of $S(f)$, $p$ must be in $S(f)$ because $f(p)$ must be greater than 1.
      intros p hp hpn
      have h_fp_gt_one : f p > 1 := by
        have := h n p;
        replace := this.of_dvd ( PNat.dvd_iff.mp hpn );
        rw [ Nat.ModEq, Nat.pow_mod ] at this; rcases p with ( _ | _ | p ) <;> rcases n with ( _ | _ | n ) <;> norm_num at *;
        · contradiction;
        · exact lt_of_le_of_ne ( PNat.one_le _ ) ( Ne.symm <| by intro t; simp ( config := { decide := Bool.true } ) [ t ] at this );
      -- Since $p$ is a prime and $f(p) > 1$, we can conclude that $p \\in S(f)$ by definition.
      exact ⟨hp, h_fp_gt_one⟩;
    exact fun p pp p2 hpn => p2 <| hS.subset ( h_prime_in_S p pp hpn );
  -- Since $f(n)$ has no prime factors other than 2, it must be a power of 2.
  have h_prime_factors_two : ∀ p : ℕ, Nat.Prime p → p ∣ (f n : ℕ) → p = 2 := by
    exact fun p pp dp => Classical.not_not.1 fun hp => h_prime_factors ⟨ p, pp.pos ⟩ pp ( ne_of_apply_ne PNat.val hp ) ( PNat.dvd_iff.2 dp );
  rw [ ← Nat.prod_primeFactorsList ( PNat.ne_zero ( f n ) ) ];
  rw [ List.prod_eq_pow_single 2 ] <;> aesop;
  exact?

/-
For a bonza function $f$, any prime $q \\notin S$ must satisfy $q \\equiv 1 \\pmod{p}$ for all $p \\in S$.
-/
lemma S_definition (f : ℕ+ → ℕ+) (h : isBonza f) (q : ℕ+) (hq_prime : Nat.Prime (q : ℕ))
    (hq_not_in_S : q ∉ S f) (p : ℕ+) (hp_in_S : p ∈ S f) :
  (q : ℕ) ≡ 1 [MOD p] := by
  -- Let's substitute $b = q$ into Lemma fermat_congruence.
  have h_subst : (f q : ℕ) ≡ q [MOD p] := by
    exact?;
  -- From Lemma odd_n_gives_f_n_one, we know that $f(q) = 1$.
  have h_fq_one : f q = 1 := by
    unfold S at *; aesop;
  exact h_subst.symm.trans ( by simp? ( config := { decide := Bool.true } ) [ h_fq_one ] )

/-
If $f$ is a bonza function and the set $S$ is finite and non-empty, then $S=\\{2\\}$.
-/
lemma finite_S_constraint (f : ℕ+ → ℕ+) (h : isBonza f) (hS_fin : (S f).Finite)
    (hS_nonempty : (S f).Nonempty) :
  S f = {(2 : ℕ+)} := by
  -- Suppose $S$ is non-empty and finite. If $S \\neq \\{2\\}$, it must contain an odd prime, and therefore also 2.
  by_cases h_odd_prime : ∃ p ∈ S f, p ≠ 2;
  · -- Let $M = \\prod_{p \\in S} p$. Any prime $q \\notin S$ must satisfy $q \\equiv 1 \\pmod M$.
    obtain ⟨p, hp_in_S, hp_odd⟩ : ∃ p ∈ S f, p ≠ 2 := h_odd_prime
    have hM : ∀ q : ℕ+, Nat.Prime (q : ℕ) → q ∉ S f → (q : ℕ) ≡ 1 [MOD ∏ p in hS_fin.toFinset, (p : ℕ)] := by
      intros q hq_prime hq_not_in_S
      have hq_cong : ∀ p ∈ S f, (q : ℕ) ≡ 1 [MOD p] := by
        exact?;
      simp_all ( config := { decide := Bool.true } ) [ Nat.modEq_iff_dvd ];
      convert Finset.prod_dvd_of_coprime _ _ <;> aesop;
      intros p hp q hq hpq; specialize hq_cong p hp; specialize hq_cong ; aesop;
      refine' Int.gcd_eq_one_iff_coprime.mp _;
      have := Nat.coprime_primes ( show Nat.Prime ( p : ℕ ) from by cases hp; aesop ) ( show Nat.Prime ( q : ℕ ) from by cases hq; aesop ) ; aesop;
    -- Let $M = \\prod_{p \\in S} p$. If $M > 2$, then $M-1 > 1$ and must have a prime divisor $q$.
    set M := ∏ p in hS_fin.toFinset, (p : ℕ)
    have hM_gt_two : M > 2 → False := by
      intro hM_gt_two
      obtain ⟨q, hq_prime, hq_div⟩ : ∃ q : ℕ+, Nat.Prime (q : ℕ) ∧ (q : ℕ) ∣ (M - 1) := by
        exact ⟨ ⟨ Nat.minFac ( M - 1 ), Nat.minFac_pos _ ⟩, Nat.minFac_prime ( Nat.ne_of_gt <| lt_tsub_iff_left.mpr <| by linarith ), Nat.minFac_dvd _ ⟩;
      -- Since $q \\mid M - 1$, we have $q \\equiv 1 \\pmod M$.
      have hq_mod : (q : ℕ) ≡ 1 [MOD M] := by
        apply hM q hq_prime;
        intro hq_in_S;
        have := Nat.dvd_sub' ( show ( q : ℕ ) ∣ M from Finset.dvd_prod_of_mem _ <| hS_fin.mem_toFinset.mpr hq_in_S ) hq_div;
        rw [ Nat.sub_sub_self ( by linarith ) ] at this ; aesop;
      have := Nat.modEq_iff_dvd.mp hq_mod.symm;
      exact absurd ( Int.le_of_dvd ( by simpa using hq_prime.one_lt ) this ) ( by norm_num; linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ M ), Nat.le_of_dvd ( Nat.sub_pos_of_lt ( by linarith : 1 < M ) ) hq_div ] );
    contrapose! hM_gt_two; aesop;
    -- Since $p \\in S$ and $p \\neq 2$, we have $p \\geq 3$.
    have hp_ge_three : 3 ≤ (p : ℕ) := by
      exact lt_of_le_of_ne ( Nat.succ_le_of_lt ( show ( p : ℕ ) > 1 from Nat.Prime.one_lt hp_in_S.1 ) ) ( Ne.symm <| by simpa only [ Ne, ← PNat.coe_inj ] using hp_odd );
    exact lt_of_lt_of_le hp_ge_three <| Nat.le_of_dvd ( Finset.prod_pos fun x hx => Nat.cast_pos.mpr <| PNat.pos x ) <| Finset.dvd_prod_of_mem _ <| hS_fin.mem_toFinset.mpr hp_in_S;
  · exact Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ hS_nonempty, fun p hp => Classical.not_not.1 fun hp' => h_odd_prime ⟨ p, hp, hp' ⟩ ⟩

/-
If $f$ is a bonza function for which $S=\\{2\\}$, and $n=2^k m$ with $m$ odd and $k \\ge 1$, then $v_2(f(n)) \\le k+2$, where $v_2(x)$ denotes the exponent of the highest power of 2 dividing $x$.
-/
lemma v2_bound_formula (f : ℕ+ → ℕ+) (h : isBonza f) (hS : S f = {(2 : ℕ+)}) (n : ℕ+)
    (k m : ℕ) (hk : k ≥ 1) (hm_odd : Odd m) (hn_def : (n : ℕ) = 2 ^ k * m) :
  padicValNat 2 (f n : ℕ) ≤ k + 2 := by
  -- By Lemma~\\ref{lem:even_n_power_of_two}, $f(n)$ must be a power of 2. Let's write $f(n)=2^\\ell$.
  have h_fn_power_of_two : ∃ ℓ : ℕ, (f n : ℕ) = 2 ^ ℓ := by
    -- By Lemma~\\ref{lem:even_n_power_of_two}, $f(n)$ must be a power of 2. Let's write $f(n)=2^{\\ell}$.
    have := even_n_power_of_two f h hS n (show Even (n : ℕ) from by
      exact hn_def ▸ even_iff_two_dvd.mpr ( dvd_mul_of_dvd_left ( pow_dvd_pow _ hk ) _ ));
    aesop;
  -- However, we can also apply the divisibility condition with $n$ and any odd prime $p$. For an odd prime $p$, $P(n,p)$ implies $f(n) \\mid p^n - 1$.
  have h_divides_odd_prime : ∀ p : ℕ+, Nat.Prime (p : ℕ) → p ≠ 2 → (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - 1 := by
    intros p hp_prime hp_ne_two
    have h_divides_p : (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - (f p : ℕ) ^ (f n : ℕ) := by
      have := h n p;
      rw [ ← Nat.modEq_zero_iff_dvd ];
      cases le_total ( ( p : ℕ ) ^ ( n : ℕ ) ) ( ( f p : ℕ ) ^ ( f n : ℕ ) ) <;> simp_all ( config := { decide := Bool.true } ) [ ← ZMod.eq_iff_modEq_nat ];
    -- Since $p$ is an odd prime, we have $f(p) = 1$ by definition of $S$.
    have h_fp_one : f p = 1 := by
      simp_all ( config := { decide := Bool.true } ) [ Set.eq_singleton_iff_unique_mem ];
      exact le_antisymm ( not_lt.mp fun contra => hp_ne_two <| hS.2 p ⟨ hp_prime, contra ⟩ ) bot_le;
    aesop;
  -- Applying this with $p=3$, we have $f(n) \\mid 3^n - 1 = 3^{2^km} - 1$.
  have h_divides_three : (f n : ℕ) ∣ 3 ^ (2 ^ k * m) - 1 := by
    simpa [ hn_def ] using h_divides_odd_prime 3 Nat.prime_three ( by decide );
  -- Using the lemma on the 2-adic valuation of $3^{2^t}-1$, we have $v_2(3^{2^k m}-1) = v_2(3^{2^k}-1) + v_2(m)$.
  have h_val_three : (padicValNat 2 (3 ^ (2 ^ k * m) - 1)) = (padicValNat 2 (3 ^ (2 ^ k) - 1)) + (padicValNat 2 m) := by
    -- Applying the lemma on the 2-adic valuation of $3^{2^t}-1$, we can simplify the expression.
    have h_val_simplified : padicValNat 2 (3 ^ (2 ^ k * m) - 1) = padicValNat 2 ((3 ^ (2 ^ k) - 1) * (∑ i in Finset.range m, (3 ^ (2 ^ k)) ^ i)) := by
      zify;
      norm_num [ mul_geom_sum, pow_mul ];
    rw [ h_val_simplified, padicValNat.mul ] <;> norm_num;
    · rw [ padicValNat.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd ] <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Finset.sum_nat_mod ];
      · exact Nat.odd_iff.mp hm_odd;
      · exact Nat.odd_iff.mp hm_odd;
    · exact ne_of_gt ( Nat.sub_pos_of_lt ( one_lt_pow₀ ( by decide ) ( by positivity ) ) );
    · exact ⟨ 0, hm_odd.pos ⟩;
  -- Using the lemma on the 2-adic valuation of $3^{2^t}-1$, we have $v_2(3^{2^k}-1) = k+2$.
  have h_val_three_k : (padicValNat 2 (3 ^ (2 ^ k) - 1)) = k + 2 := by
    refine' Nat.le_induction _ _ k hk;
    · native_decide;
    · intro n hn ih; rw [ show ( 3 : ℕ ) ^ 2 ^ ( n + 1 ) - 1 = ( 3 ^ 2 ^ n - 1 ) * ( 3 ^ 2 ^ n + 1 ) by convert Nat.sq_sub_sq ( 3 ^ 2 ^ n ) 1 using 1 <;> ring ] ; rw [ padicValNat.mul ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ ( by decide ) ( by positivity ) ) ) ( by positivity ) ] ; simp +arith +decide [ ih ] ;
      rw [ padicValNat ];
      norm_num [ Nat.find_eq_iff ];
      exact ⟨ by rw [ Nat.dvd_iff_mod_eq_zero ] ; rcases n with ( _ | _ | n ) <;> norm_num [ Nat.add_mod, Nat.pow_succ', Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *, by rw [ ← even_iff_two_dvd ] ; simp ( config := { decide := Bool.true } ) [ parity_simps ] ⟩;
  have := Nat.factorization_le_iff_dvd ( by aesop ) ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ ( by decide : 1 < 3 ) ( by aesop ) ) ) |>.2 h_divides_three ; aesop;
  simp_all ( config := { decide := Bool.true } ) [ Nat.factorization ];
  replace := this 2 ; simp_all ( config := { decide := Bool.true } );
  erw [ padicValNat.eq_zero_of_not_dvd ( by simpa [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ] using hm_odd ) ] at this ; linarith

/-
If $f$ is a bonza function, then $f(n) \\le 4n$ for all $n \\in \\mathbb{N}$.
-/
lemma upper_bound_four (f : ℕ+ → ℕ+) (h : isBonza f) (n : ℕ+) :
  (f n : ℕ) ≤ 4 * (n : ℕ) := by
  -- Consider two cases: $S$ is finite or infinite.
  by_cases hS_finite : (S f).Finite;
  · -- If $S$ is non-empty and finite, then $S=\\{2\\}$.
    by_cases hS_nonempty : (S f).Nonempty;
    · -- Since $S = \\{2\\}$, we can use the results from the lemmas. For any $n$, if $n$ is odd, then $f(n) = 1$, which is trivially $\\leq 4n$. If $n$ is even, then $f(n)$ is a power of 2.
      have h_even : ∀ n : ℕ+, Even (n : ℕ) → (f n : ℕ) ≤ 4 * (n : ℕ) := by
        -- Since $S = \\{2\\}$, we can use the results from the lemmas. For any $n$, if $n$ is even, then $f(n)$ is a power of 2.
        intros n hn_even
        obtain ⟨k, hk⟩ : ∃ k : ℕ, (f n : ℕ) = 2 ^ k := by
          have := even_n_power_of_two f h ( by
            apply finite_S_constraint;
            · assumption;
            · assumption;
            · assumption ) n hn_even;
          exact this;
        -- Since $n$ is even, we can write $n = 2^m \\cdot l$ where $l$ is odd and $m \\geq 1$.
        obtain ⟨m, l, hm, hl⟩ : ∃ m l : ℕ, m ≥ 1 ∧ Odd l ∧ (n : ℕ) = 2 ^ m * l := by
          use Nat.factorization n 2, n / 2 ^ Nat.factorization n 2;
          -- Since $n$ is even, its factorization must include at least one 2, so $m \\geq 1$.
          have hm_ge_one : 1 ≤ Nat.factorization n 2 := by
            exact Nat.pos_of_ne_zero fun h => by simp_all ( config := { decide := Bool.true } ) [ even_iff_two_dvd, Nat.factorization_eq_zero_iff ] ;
          exact ⟨ hm_ge_one, by rw [ Nat.odd_iff ] ; exact Nat.mod_two_ne_zero.mp fun contra => absurd ( Nat.dvd_of_mod_eq_zero contra ) ( Nat.not_dvd_ord_compl ( by norm_num ) <| by aesop ), Eq.symm <| Nat.mul_div_cancel' <| Nat.ord_proj_dvd _ _ ⟩;
        -- By Lemma~\\ref{lem:v2_bound_formula}, we have $v_2(f(n)) \\le m + 2$.
        have h_v2_bound : k ≤ m + 2 := by
          have h_v2_bound : padicValNat 2 (f n : ℕ) ≤ m + 2 := by
            -- Applying Lemma~\\ref{lem:v2_bound_formula} with $n = 2^m \\cdot l$, we get $v_2(f(n)) \\le m + 2$.
            apply v2_bound_formula;
            any_goals tauto;
            exact?;
          simp_all ( config := { decide := Bool.true } ) [ padicValNat.pow ];
        aesop;
        exact le_trans ( pow_le_pow_right₀ ( by decide ) h_v2_bound ) ( by ring_nf; norm_num; nlinarith [ pow_pos ( by decide : 0 < ( 2 : ℕ ) ) m, left.pos ] );
      -- For any odd integer $n$, if $n > 1$, then $f(n) = 1$ by the lemma odd_n_gives_f_n_one. If $n = 1$, then $f(1) = 1$ by the lemma f_one_equals_one.
      have h_odd : ∀ n : ℕ+, Odd (n : ℕ) → (f n : ℕ) ≤ 4 * (n : ℕ) := by
        intros n hn_odd
        by_cases hn_gt_one : n > 1;
        · have := odd_n_gives_f_n_one f h ( show S f = { ( 2 : ℕ+ ) } from ?_ ) n hn_odd hn_gt_one;
          · aesop;
            linarith [ PNat.pos n ];
          · exact?;
        · have := h 1 1 ; simp_all ( config := { decide := Bool.true } ) [ Nat.ModEq, Nat.pow_mod ];
      exact if hn : Even ( n : ℕ ) then h_even n hn else h_odd n ( by simpa using hn );
    · -- If $S$ is empty, then $f(p)=1$ for all prime numbers $p$. The condition $P(n,p)$ implies $f(n) \\mid p^n - f(p)^{f(n)} = p^n - 1$. Since this holds for all primes $p$, we must have $f(n)=1$.
      have h_empty_S : ∀ p : ℕ+, Nat.Prime (p : ℕ) → f p = 1 := by
        aesop;
        exact le_antisymm ( not_lt.mp fun contra => hS_nonempty ⟨ p, a, contra ⟩ ) bot_le;
      -- The condition $P(n,p)$ implies $f(n) \\mid p^n - f(p)^{f(n)} = p^n - 1$. Since this holds for all primes $p$, we must have $f(n)=1$.
      have h_divides_one : ∀ p : ℕ+, Nat.Prime (p : ℕ) → (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - 1 := by
        intro p hp; specialize h n p; aesop;
        simpa [ ← Int.natCast_dvd_natCast, Nat.cast_sub ( Nat.one_le_pow _ _ hp.pos ) ] using h.symm.dvd;
      -- Since this holds for all primes $p$, we must have $f(n)=1$.
      have h_fn_one : f n = 1 := by
        -- Assume for contradiction that $f(n) > 1$. Then there exists a prime $q$ such that $q \\mid f(n)$.
        by_contra h_contra
        obtain ⟨q, hq_prime, hq_div⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ (f n : ℕ) := by
          exact Nat.exists_prime_and_dvd ( by simpa using h_contra );
        have := Nat.dvd_trans hq_div ( h_divides_one ⟨ q, hq_prime.pos ⟩ hq_prime );
        haveI := Fact.mk hq_prime; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub ( Nat.one_le_pow _ _ hq_prime.pos ) ] ;
      simp ( config := { decide := Bool.true } ) [ h_fn_one ];
      linarith [ PNat.pos n ];
  · -- If $f$ is a bonza function for which $S$ is infinite, then $f(n) \\le n$ for all $n \\in \\mathbb{N}$.
    have infinite_S_constraint (f : ℕ+ → ℕ+) (h : isBonza f) (hS_inf : (S f).Infinite) :
      ∀ n : ℕ+, (f n : ℕ) ≤ n := by
        -- Take any $n$. Since $S$ is infinite, there exists a prime $p \\in S$ such that $p > f(n)$.
        intro n
        obtain ⟨p, hpS, hp_gt⟩ : ∃ p ∈ S f, (p : ℕ) > (f n : ℕ) := by
          exact Exists.elim ( hS_inf.exists_gt ( f n ) ) fun p hp => ⟨ p, hp.1, hp.2 ⟩;
        -- By Lemma~\\ref{lem:fermat_congruence}, $f(n) \\equiv n \\pmod{p}$.
        have h_congr : (f n : ℕ) ≡ (n : ℕ) [MOD p] := by
          exact?;
        rw [ Nat.ModEq ] at h_congr;
        contrapose! h_congr;
        rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith;
    exact le_trans ( infinite_S_constraint f h hS_finite n ) ( le_mul_of_one_le_left' ( by decide ) )

/-
Let $\\mathbb{N}$ denote the set of positive integers. A function $f\\colon\\mathbb{N} \\to \\mathbb{N}$ is said to be \\emph{bonza} if
$$f(a) \\text{ divides } b^a - f(b)^{f(a)}$$
for all positive integers $a$ and $b$.
The smallest real constant $c$ such that $f(n) \\leq cn$ for all bonza functions $f$ and all positive integers $n$ is $4$.
-/
theorem main_theorem (IsBonza : (ℕ+ → ℕ+) → Prop)
  (hisBonza : ∀ f, IsBonza f ↔ ∀ a b : ℕ+, (b : ℕ) ^ (a : ℕ) ≡ (f b : ℕ) ^ (f a : ℕ) [MOD f a]) :
  IsLeast {c : ℝ | ∀ f, IsBonza f → ∀ n : ℕ+, (f n : ℝ) ≤ c * (n : ℝ)} 4 := by
  -- To prove that 4 is the least such constant, we need to show that for any $c < 4$, there exists a bonza function $f$ and an $n$ such that $f(n) > cn$.
  have h_least : ∀ c : ℝ, c < 4 → ∃ f : ℕ+ → ℕ+, IsBonza f ∧ ∃ n : ℕ+, (f n : ℝ) > c * (n : ℝ) := by
    -- For any $c < 4$, we can choose the bonza function $f$ defined by $f(n) = 1$ if $n$ is odd, $f(n) = 4$ if $n \\equiv 2 \\pmod{4}$, and $f(n) = 16$ if $n \\equiv 0 \\pmod{4}$, and $n = 4$.
    intros c hc
    use f_construction;
    constructor;
    · exact hisBonza _ |>.2 construction_bonza;
    · exact ⟨ 4, show c * 4 < 16 by linarith ⟩;
  constructor;
  · aesop;
    exact_mod_cast upper_bound_four f ( by aesop ) n;
  · exact fun c hc => by contrapose! h_least; tauto;

#print axioms main_theorem
`,M=`/-
A proper divisor of a positive integer $N$ is a positive divisor of $N$ other than $N$ itself.
The infinite sequence $a_1,a_2,\\dots$ consists of positive integers, each of which has at least three proper divisors.
For each $n\\geqslant 1$, the integer $a_{n+1}$ is the sum of the three largest proper divisors of $a_n$.
Determine all possible values of $a_1$.
Answer: All integers of the form $6 \\cdot 12^a \\cdot m$, for $a \\geq 0$ and $m$ is coprime to 10.
-/

import HarmonicLean.Imports

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace IMO2025P4

/-
Let $N$ be a positive integer with at least three proper divisors. Let its positive divisors in ascending order be $1=c_1 < c_2 < c_3 < c_4 < \\dots$. The three largest proper divisors of $N$ are $N/c_2, N/c_3, N/c_4$. We define the function $S(N)$ as the sum of these three divisors: $S(N) = \\frac{N}{c_2} + \\frac{N}{c_3} + \\frac{N}{c_4}$. The sequence in the problem is defined by $a_{n+1} = S(a_n)$.
-/
def S (N : ℕ) : ℕ :=
  let largestProperDivisors := (Nat.properDivisors N).sort (· ≥ ·)
  largestProperDivisors[0]! + largestProperDivisors[1]! + largestProperDivisors[2]!

/-
For a positive integer $N$ satisfying the conditions in Definition~\\ref{def:sequence_function}, we define the ratio $R(N) = \\frac{S(N)}{N} = \\frac{1}{c_2} + \\frac{1}{c_3} + \\frac{1}{c_4}$. The sequence recurrence can be written as $a_{n+1} = a_n R(a_n)$.
-/
def R (N : ℕ) : ℚ :=
  (S N : ℚ) / (N : ℚ)

/-
For a positive integer $N$, let $c_k(N)$ denote its $k$-th smallest positive divisor. So $c_1(N)=1 < c_2(N) < c_3(N) < \\dots$. We will write $c_k$ when $N$ is clear from the context. The condition that $N$ has at least three proper divisors means its total number of divisors, $\\tau(N)$, is at least 4. This guarantees the existence of $c_4$.
-/
def c_k (k N : ℕ) : ℕ :=
  ((Nat.divisors N).sort (· ≤ ·))[k-1]!

-- A helper definition for the properties of the sequence \`a\`
def IsSequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧
  (∀ n, 3 ≤ (Nat.properDivisors (a n)).card) ∧
  (∀ n, a (n+1) = S (a n))

/-
If $a_n$ is an odd integer, then $a_{n+1}$ is also an odd integer.
-/
lemma lem_odd_successor_is_odd (a_n : ℕ) : Odd a_n → 3 ≤ (Nat.properDivisors a_n).card → Odd (S a_n) := by
  aesop;
  -- Since $a_n$ is odd, all its proper divisors are also odd.
  have h_proper_divisors_odd : ∀ d ∈ ((Nat.properDivisors a_n).sort (· ≥ ·)), Odd d := by
    aesop;
    -- Since $a_n$ is odd, any divisor $d$ of $a_n$ must also be odd. This is because if $d$ were even, then $a_n$ would be even, contradicting the assumption that $a_n$ is odd.
    exact a.of_dvd_nat left;
  -- Since $a_n$ is odd, the sum of its three largest proper divisors is also odd.
  have h_sum_odd : Odd ((Finset.sort (· ≥ ·) (Nat.properDivisors a_n))[0]! + (Finset.sort (· ≥ ·) (Nat.properDivisors a_n))[1]! + (Finset.sort (· ≥ ·) (Nat.properDivisors a_n))[2]!) := by
    rcases n : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) a_n.properDivisors with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | hz ⟩ ⟩ ⟩ ; simp_all +arith +decide;
    · replace n := congr_arg List.length n; aesop;
      interval_cases a_n <;> contradiction;
    · -- Since the cardinality of the proper divisors is at least 3, the sorted list cannot be [x].
      have h_card : (Finset.sort (fun x1 x2 => x1 ≥ x2) a_n.properDivisors).length ≥ 3 := by
        simpa using a_1;
      grind;
    · replace n := congr_arg List.length n; aesop;
    · -- Since $x$, $y$, and $z$ are all odd, their sum $x + y + z$ is also odd.
      have h_odd_sum : Odd x ∧ Odd y ∧ Odd z := by
        aesop;
      simp_all ( config := { decide := Bool.true } ) [ parity_simps ];
      exact iff_of_false ( by simpa using h_odd_sum.2.1 ) ( by simpa using h_odd_sum.2.2 );
    · simp_all ( config := { decide := Bool.true } ) [ parity_simps ];
      exact iff_of_false ( by simpa using h_proper_divisors_odd.2.1 ) ( by simpa using h_proper_divisors_odd.2.2.1 );
  exact h_sum_odd

/-
If a term $a_k$ in the sequence is odd, then all subsequent terms $a_n$ for $n \\ge k$ are odd.
-/
lemma lem_odd_implies_all_odd (a : ℕ → ℕ) (k : ℕ) : IsSequence a → Odd (a k) → ∀ n, k ≤ n → Odd (a n) := by
  -- We proceed by induction on $n$.
  intro h_seq h_odd_k n hn
  induction' hn with n ih;
  · assumption;
  · cases h_seq ; aesop;
    exact?

/-
For an odd integer $N$ with at least three proper divisors, $R(N) < 1$.
-/
lemma lem_ratio_for_odd (N : ℕ) : Odd N → 3 ≤ (Nat.properDivisors N).card → R N < 1 := by
  -- By Lemma~\\ref{lem:odd_successor_divisors}, all divisors of $N$ are odd.
  intros h_odd h_card
  have h_divisors_odd : ∀ d, d ∈ Nat.properDivisors N → Odd d := by
    exact fun d hd => h_odd.of_dvd_nat <| Nat.mem_properDivisors.mp hd |>.1;
  unfold R;
  rw [ div_lt_iff₀ ] <;> norm_cast;
  · -- Let $d_1$, $d_2$, and $d_3$ be the three largest proper divisors of $N$. Then $d_1 \\leq N/3$, $d_2 \\leq N/3$, and $d_3 \\leq N/3$.
    obtain ⟨d1, d2, d3, hd1, hd2, hd3, hd_sum⟩ : ∃ d1 d2 d3, d1 ∈ Nat.properDivisors N ∧ d2 ∈ Nat.properDivisors N ∧ d3 ∈ Nat.properDivisors N ∧ d1 > d2 ∧ d2 > d3 ∧ d1 + d2 + d3 = S N := by
      unfold S;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with _ | ⟨ d1, _ | ⟨ d2, _ | ⟨ d3, _ | k ⟩ ⟩ ⟩ ; aesop;
      · replace x := congr_arg List.length x; aesop;
        interval_cases N <;> contradiction;
      · replace x := congr_arg List.length x; aesop;
      · replace x := congr_arg List.length x; aesop;
      · -- Since the list is sorted in descending order, we have $d1 > d2$ and $d2 > d3$.
        have h_sorted : d1 > d2 ∧ d2 > d3 := by
          have := Finset.sort_sorted_gt N.properDivisors; aesop;
        exact ⟨ d1, d2, d3, by replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x d1; aesop, by replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x d2; aesop, by replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x d3; aesop, h_sorted.1, h_sorted.2, rfl ⟩;
      · have := Finset.sort_sorted ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors; aesop;
        -- Since $d1$, $d2$, and $d3$ are the three largest proper divisors of $N$, we have $d1 > d2 > d3$.
        have h_distinct : d1 > d2 ∧ d2 > d3 := by
          have h_distinct : d1 ≠ d2 ∧ d2 ≠ d3 := by
            have h_distinct : List.Nodup (d1 :: d2 :: d3 :: k :: tail) := by
              exact x ▸ Finset.sort_nodup _ _;
            aesop;
          exact ⟨ lt_of_le_of_ne left h_distinct.1.symm, lt_of_le_of_ne left_1 h_distinct.2.symm ⟩;
        exact ⟨ d1, ⟨ Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.1, Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.2 ⟩, d2, ⟨ Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.1, Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.2 ⟩, d3, ⟨ Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.1, Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.2 ⟩, by linarith, by linarith, rfl ⟩;
    -- Since $d_1$, $d_2$, and $d_3$ are the three largest proper divisors of $N$, each must be less than or equal to $N/3$.
    have hd1_le : d1 ≤ N / 3 := by
      -- Since $d1$ is a proper divisor of $N$, there exists some integer $k$ such that $N = d1 * k$ and $k > 1$.
      obtain ⟨k, hk⟩ : ∃ k, N = d1 * k ∧ 1 < k := by
        norm_num +zetaDelta at *;
        exact hd1.1.imp fun x hx => ⟨ by linarith, by nlinarith only [ hx, hd1.2 ] ⟩;
      rw [ Nat.le_div_iff_mul_le three_pos ] ; rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
      · exact absurd h_odd ( by simp ( config := { decide := Bool.true } ) [ parity_simps ] );
      · nlinarith only [ hd1 ]
    have hd2_le : d2 ≤ N / 3 := by
      grind
    have hd3_le : d3 ≤ N / 3 := by
      grind;
    rw [ Nat.le_div_iff_mul_le three_pos ] at *;
    bound;
  · exact?

/-
If a term $a_k$ in the sequence is odd, the subsequence $(a_n)_{n \\ge k}$ is strictly decreasing.
-/
lemma lem_odd_implies_decreasing (a : ℕ → ℕ) (k : ℕ) : IsSequence a → Odd (a k) → ∀ n ≥ k, a (n+1) < a n := by
  -- By definition of IsSequence, we know that R(a_n) < 1 for all n ≥ k.
  intros ha h_odd n hn
  have h_ratio : R (a n) < 1 := by
    -- Since $a_n$ is odd for all $n \\geq k$, we can apply the lemma that states $R(N) < 1$ for any odd $N$ with at least three proper divisors.
    have h_odd_all : ∀ n ≥ k, Odd (a n) := by
      exact?;
    -- Apply the lemma that states $R(N) < 1$ for any odd $N$ with at least three proper divisors.
    apply lem_ratio_for_odd; exact h_odd_all n hn; exact ha.2.1 n;
  -- By definition of $R$, we know that $R(a_n) = \\frac{S(a_n)}{a_n}$. Since $R(a_n) < 1$, multiplying both sides by $a_n$ (which is positive) gives $S(a_n) < a_n$.
  have h_S_lt_an : S (a n) < a n := by
    unfold R at h_ratio;
    rw [ div_lt_one ] at h_ratio <;> norm_cast at * ; linarith [ ha.1 n ];
  rw [ ha.2.2 ] ; aesop

/-
An infinite sequence as defined in the problem cannot contain any odd terms.
-/
lemma lem_no_odd_terms (a : ℕ → ℕ) : IsSequence a → ∀ k, Even (a k) := by
  -- Assume that there exists some k where a_k is odd.
  by_contra h_odd;
  -- Then there exists some k such that a_k is odd and the sequence a is an IsSequence.
  obtain ⟨k, hk_odd, ha_seq⟩ : ∃ k, Odd (a k) ∧ IsSequence a := by
    aesop;
  -- By Lemma~\\ref{lem:odd_implies_decreasing}, the sequence of positive integers $(a_n)_{n \\ge k}$ is strictly decreasing.
  have h_decreasing : ∀ n ≥ k, a (n + 1) < a n := by
    exact?;
  -- Apply the fact that a strictly decreasing sequence of positive integers must be finite.
  have h_finite : Set.Finite (Set.range (fun n => a (k + n))) := by
    -- Since the sequence $a$ is strictly decreasing starting from $k$, the values $a (k + n)$ are all distinct and decreasing. Therefore, the range of the function $n \\mapsto a (k + n)$ is finite.
    have h_finite : ∀ n, a (k + n) ≥ a (k + (n + 1)) := by
      exact fun n => Nat.le_of_lt ( h_decreasing _ ( Nat.le_add_right _ _ ) );
    exact Set.finite_iff_bddAbove.mpr ⟨ a ( k + 0 ), by rintro x ⟨ n, rfl ⟩ ; exact Nat.recOn n ( by norm_num ) fun n ihn => by linarith! [ h_finite n ] ⟩;
  exact h_finite.not_infinite <| Set.infinite_range_of_injective ( StrictAnti.injective <| strictAnti_nat_of_succ_lt fun n => h_decreasing _ <| Nat.le_add_right _ _ )

/-
Every term $a_n$ in the sequence must be an even integer.
-/
lemma lem_all_terms_even (a : ℕ → ℕ) : IsSequence a → ∀ n, Even (a n) := by
  exact?

/-
For any term $a_n$ in the sequence, its second smallest divisor is $c_2(a_n)=2$.
-/
lemma lem_c2_is_2 (a : ℕ → ℕ) : IsSequence a → ∀ n, c_k 2 (a n) = 2 := by
  -- By Lemma~\\ref{lem:all_terms_even}, each term $a_n$ is even. Therefore, $2$ is a divisor of $a_n$.
  have h_two_divisor (a : ℕ → ℕ) (n : ℕ) (ha : IsSequence a) : 2 ∈ Nat.divisors (a n) := by
    norm_num +zetaDelta at *;
    exact ⟨ even_iff_two_dvd.mp ( by exact? ), ne_of_gt ( ha.1 n ) ⟩;
  -- Since $a_n$ is even, its smallest divisor is $1$ and the next smallest divisor is $2$.
  have h_smallest_divisors (a : ℕ → ℕ) (n : ℕ) (ha : IsSequence a) : (Nat.divisors (a n)).sort (· ≤ ·) = 1 :: 2 :: (Nat.divisors (a n) \\ {1, 2}).sort (· ≤ ·) := by
    -- Since the divisors are sorted in ascending order, the first element is 1, the second is 2, and the rest are the divisors greater than 2.
    have h_sorted : (Nat.divisors (a n)).sort (· ≤ ·) = (insert 1 (insert 2 ((Nat.divisors (a n)) \\ {1, 2}))).sort (· ≤ ·) := by
      congr;
      ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> aesop;
    rw [ h_sorted, Finset.sort_insert, Finset.sort_insert ];
    · exact fun x hx => Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩;
    · aesop;
    · aesop;
      exact Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero ( h_two_divisor a n ha |>.2 ) );
    · aesop;
  unfold c_k; aesop;

/-
A term $a_n$ is a fixed point, i.e., $a_{n+1}=a_n$, if and only if $R(a_n)=1$.
-/
lemma lem_fixed_point_condition (N : ℕ) : 0 < N → (S N = N ↔ R N = 1) := by
  unfold R;
  intro N; rw [ div_eq_iff ] ; norm_cast ; aesop;
  positivity

/-
An integer $N$ has smallest divisors $c_2=2, c_3=3, c_4=6$ if and only if it is divisible by 6, not divisible by 4, and not divisible by 5.
-/
lemma lem_structure_of_fixed_points (N : ℕ) : 0 < N → (Nat.divisors N).card ≥ 4 → ((c_k 2 N = 2 ∧ c_k 3 N = 3 ∧ c_k 4 N = 6) ↔ (6 ∣ N ∧ ¬ (4 ∣ N) ∧ ¬ (5 ∣ N))) := by
  bound;
  -- Since $N$ is divisible by 6, it must be divisible by both 2 and 3. Therefore, the smallest divisors after 1 are 2 and 3.
  have h_div_2_3 : 2 ∣ N ∧ 3 ∣ N := by
    unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ ) <;> aesop;
    · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 2; aesop;
    · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 3; aesop;
  exact Nat.lcm_dvd h_div_2_3.left h_div_2_3.right;
  · unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    · have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
      have := this 1; have := this.symm; aesop;
      cases this_1 6 ; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      have := n ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ a_2, by linarith ⟩ ) ; aesop;
      linarith [ left_7 4 h_2 ];
  · unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    · have := Finset.sort_sorted ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
      interval_cases x <;> have := congr_arg List.toFinset n <;> norm_num [ Finset.ext_iff ] at this;
      · specialize this 0 ; aesop;
      · exact absurd ( this 5 ) ( by norm_num [ a_2, a.ne' ] );
      · have := this 1; aesop;
    · -- Since 5 is a divisor of N and the list is sorted, 5 must appear between 3 and 6 in the list.
      have h_five_in_list : 5 ∈ Finset.sort (fun x1 x2 => x1 ≤ x2) N.divisors := by
        exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.mpr ⟨ a_2, by linarith ⟩ );
      have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      linarith [ left_7 5 h_2 ];
  · -- Since $N$ is divisible by 6, it is even, so 2 is a divisor. The smallest divisor is 1, so the next one must be 2.
    have h_divisors : 1 ∈ Nat.divisors N ∧ 2 ∈ Nat.divisors N ∧ ∀ d ∈ Nat.divisors N, 1 < d → d ≥ 2 := by
      exact ⟨ Nat.mem_divisors.mpr ⟨ one_dvd _, by linarith ⟩, Nat.mem_divisors.mpr ⟨ dvd_trans ( by decide ) left, by linarith ⟩, fun d hd hd' => hd' ⟩;
    -- Since the divisors are sorted in ascending order and 2 is the smallest divisor greater than 1, the second element in the sorted list of divisors must be 2.
    have h_sorted : (Nat.divisors N).sort (· ≤ ·) = 1 :: 2 :: (Nat.divisors N \\ {1, 2}).sort (· ≤ ·) := by
      rw [ ← Finset.sort_insert ];
      · rw [ ← Finset.sort_insert ];
        · congr;
          ext d; by_cases hd1 : d = 1 <;> by_cases hd2 : d = 2 <;> aesop;
        · aesop;
          exact Nat.pos_of_dvd_of_pos left_2 a;
        · norm_num +zetaDelta at *;
      · exact fun d hd => h_divisors.2.2 d ( by aesop ) ( lt_of_le_of_ne ( Nat.pos_of_mem_divisors ( by aesop ) ) ( Ne.symm ( by aesop ) ) );
      · aesop;
    -- Since the list is sorted in ascending order, the second element is indeed 2.
    have h_second : ((Nat.divisors N).sort (· ≤ ·))[1]! = 2 := by
      aesop;
    exact h_second;
  · -- Since $N$ is divisible by 6, its divisors include 1, 2, 3, and 6. The next smallest divisor after 3 is 6, so the third smallest divisor is 3.
    have h_divisors : (Nat.divisors N).sort (· ≤ ·) = [1, 2, 3] ++ (Nat.divisors N \\ {1, 2, 3}).sort (· ≤ ·) := by
      -- Since $N$ is divisible by 6, its divisors include 1, 2, 3, and 6. The next smallest divisor after 3 is 6, so the third smallest divisor is 3. Therefore, the sorted list of divisors of $N$ is [1, 2, 3] followed by the sorted list of divisors of $N$ excluding 1, 2, and 3.
      have h_divisors : (Nat.divisors N).sort (· ≤ ·) = (insert 1 (insert 2 (insert 3 ((Nat.divisors N) \\ {1, 2, 3})))).sort (· ≤ ·) := by
        congr;
        ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx3 : x = 3 <;> aesop;
        · exact dvd_trans ( by norm_num ) left;
        · exact dvd_trans ( by norm_num ) left;
      rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
      all_goals aesop;
      · contrapose! left_3; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
      · exact Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos left_2 a ) ( Ne.symm left_3 );
      · exact Nat.pos_of_dvd_of_pos left_2 a;
    -- Since the list of divisors is sorted in ascending order, the third element is the third smallest divisor.
    unfold c_k; aesop;
  · -- Since $N$ is divisible by 6, the divisors of $N$ include 1, 2, 3, and 6. We need to show that these are the four smallest divisors.
    have h_divisors : (Nat.divisors N).sort (· ≤ ·) = [1] ++ [2] ++ [3] ++ [6] ++ (Nat.divisors N \\ {1, 2, 3, 6} : Finset ℕ).sort (· ≤ ·) := by
      have h_divisors : (Nat.divisors N).sort (· ≤ ·) = (insert 1 (insert 2 (insert 3 (insert 6 ((Nat.divisors N) \\ {1, 2, 3, 6}))))).sort (· ≤ ·) := by
        congr;
        ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx3 : x = 3 <;> by_cases hx6 : x = 6 <;> aesop;
        · exact dvd_trans ( by norm_num ) left;
        · exact dvd_trans ( by norm_num ) left;
      rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
      all_goals simp_all ( config := { decide := Bool.true } ) [ Finset.mem_insert, Finset.mem_singleton ];
      · intro b hb _ hb1 hb2 hb3 hb6; contrapose! hb1; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
      · intro a ha _ ha1 ha2 ha3 ha6; contrapose! ha1; interval_cases a <;> simp_all ( config := { decide := Bool.true } ) ;
      · exact fun a ha _ ha1 ha2 ha3 ha6 => Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos ha ‹_› ) ( Ne.symm ha1 );
      · bound;
        exact Nat.pos_of_dvd_of_pos a_3 a;
    unfold c_k;
    aesop

/-
For any term $a_n$ in the sequence, the ratio is $R(a_n) = \\frac{1}{2} + \\frac{1}{c_3(a_n)} + \\frac{1}{c_4(a_n)}$.
-/
lemma lem_ratio_for_even (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
  unfold R c_k;
  unfold S;
  rcases N <;> aesop;
  -- Let's simplify the expression for the ratio $R$.
  have h_divisors : (Nat.divisors (Nat.succ n)).sort (· ≤ ·) = 1 :: 2 :: ((Nat.divisors (Nat.succ n)).erase 1 |>.erase 2).sort (· ≤ ·) := by
    have h_divisors : (Nat.divisors (Nat.succ n)).sort (· ≤ ·) = (insert 1 (insert 2 ((Nat.divisors (Nat.succ n)).erase 1 |>.erase 2))).sort (· ≤ ·) := by
      congr;
      ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> aesop;
      exact even_iff_two_dvd.mp a;
    rw [ h_divisors, Finset.sort_insert, Finset.sort_insert ];
    · exact fun x hx => Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩;
    · aesop;
    · field_simp;
      exact fun a ha₁ ha₂ ha₃ => Nat.pos_of_dvd_of_pos ha₃ ( Nat.succ_pos _ );
    · aesop;
  have h_divisors_rev : (Nat.divisors (Nat.succ n)).sort (· ≥ ·) = (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))) := by
    have h_divisors_rev : (Nat.divisors (Nat.succ n)).sort (· ≥ ·) = (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))) := by
      have h_divisors_rev_aux : ∀ {l : List ℕ}, (∀ d ∈ l, d ∣ Nat.succ n) → List.Sorted (· ≤ ·) l → List.Sorted (· ≥ ·) (List.map (fun d => Nat.succ n / d) l) := by
        intros l hl_div hl_sorted; induction hl_sorted <;> aesop;
        exact Nat.div_le_div_left ( a_3 _ a_6 ) ( Nat.pos_of_dvd_of_pos left ( Nat.succ_pos _ ) )
      have h_divisors_rev_aux : List.Perm (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))) ((Nat.divisors (Nat.succ n)).sort (· ≥ ·)) := by
        rw [ List.perm_iff_count ];
        intro x; rw [ List.count_eq_of_nodup, List.count_eq_of_nodup ];
        · simp +zetaDelta at *;
          bound;
          · exact False.elim <| h <| Nat.div_dvd_of_dvd left;
          · exact False.elim <| h ⟨ ( n + 1 ) / x, Nat.div_dvd_of_dvd h_1, by rw [ Nat.div_div_self h_1 <| by aesop ] ⟩;
        · exact Finset.sort_nodup _ _;
        · rw [ List.nodup_map_iff_inj_on ];
          · norm_num +zetaDelta at *;
            intro x hx y hy hxy; have := Nat.div_mul_cancel hx; have := Nat.div_mul_cancel hy; aesop;
            nlinarith;
          · exact Finset.sort_nodup _ _;
      aesop;
      have h_sorted : List.Sorted (· ≥ ·) ((n + 1) :: (n + 1) / 2 :: List.map (fun d => Nat.succ n / d) (Finset.sort (fun x1 x2 => x1 ≤ x2) (((n + 1).divisors.erase 1).erase 2))) := by
        simp +zetaDelta at *;
        exact ⟨ ⟨ Nat.div_le_self _ _, fun a x hx₁ hx₂ hx₃ hx₄ => hx₄ ▸ Nat.div_le_self _ _ ⟩, fun b x hx₁ hx₂ hx₃ hx₄ => hx₄ ▸ Nat.div_le_div_left ( show x ≥ 2 from Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos hx₃ ( Nat.succ_pos _ ) ) ( Ne.symm hx₂ ) ) ( by decide ), h_divisors_rev_aux_1 ( fun x hx => Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 hx ) <| Finset.sort_sorted ( · ≤ · ) _ ⟩;
      exact List.eq_of_perm_of_sorted h_divisors_rev_aux.symm ( Finset.sort_sorted ( fun x1 x2 => x2 ≤ x1 ) _ ) h_sorted;
    exact h_divisors_rev;
  -- Let's substitute the sorted list of divisors into the expression for $R$.
  have h_divisors_erase : (Nat.properDivisors (Nat.succ n)).sort (· ≥ ·) = (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))).tail := by
    rw [ ← h_divisors_rev ];
    rw [ ← Nat.cons_self_properDivisors ] <;> aesop;
    rw [ Finset.sort_insert ] ; aesop;
    · exact fun x hx => Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.mem_properDivisors.mp hx |>.1 );
    · aesop;
  aesop;
  rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( ( Nat.divisors ( n + 1 ) ).erase 1 |> Finset.erase <| 2 ) with _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ; aesop;
  · rw [ inv_eq_one_div, div_eq_div_iff ] <;> norm_cast <;> linarith [ Nat.div_mul_cancel ( even_iff_two_dvd.mp a ) ];
  · replace h_divisors := congr_arg List.length h_divisors ; aesop;
    rw [ ← Nat.cons_self_properDivisors ] at h_divisors <;> aesop;
  · -- Let's simplify the expression for the ratio $R$ in the case where there are at least three proper divisors.
    field_simp;
    rw [ Nat.cast_div, Nat.cast_div, Nat.cast_div ] <;> norm_num <;> ring;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k b; aesop;
      rwa [ add_comm ];
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k a; aesop;
      rwa [ add_comm ];
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · simpa [ ← even_iff_two_dvd, parity_simps ] using ‹Even ( n + 1 ) ›

/-
If $R(N)>1$ for an even number $N$ with $c_3(N)=3$, then $c_4(N)$ must be 4 or 5.
-/
lemma lem_growth_condition (N : ℕ) : Even N → c_k 3 N = 3 → R N > 1 → c_k 4 N = 4 ∨ c_k 4 N = 5 := by
  -- Since $c_k 3 N = 3$, we have $R N = \\frac{1}{2} + \\frac{1}{3} + \\frac{1}{c_k 4 N}$.
  intro h_even h_c3 h_r
  have h_r_eq : R N = (1 : ℚ) / 2 + 1 / 3 + 1 / (c_k 4 N) := by
    rw [ lem_ratio_for_even ] <;> aesop;
    -- Since $N$ is even, it has at least the proper divisors $1$, $2$, and $N/2$.
    have h_divisors : Nat.properDivisors N ⊇ {1, 2, N / 2} := by
      simp ( config := { decide := Bool.true } ) [ Finset.insert_subset_iff ];
      rcases N with ( _ | _ | _ | N ) <;> simp_all +arith +decide;
      · exact absurd h_c3 ( by native_decide );
      · exact absurd h_r ( by native_decide );
      · exact ⟨ by obtain ⟨ k, hk ⟩ := h_even; omega, Nat.div_dvd_of_dvd <| even_iff_two_dvd.mp h_even, by obtain ⟨ k, hk ⟩ := h_even; omega ⟩;
    -- Since {1, 2, N/2} is a subset of the proper divisors of N and these three elements are distinct, the cardinality of the proper divisors must be at least 3.
    have h_card : ({1, 2, N / 2} : Finset ℕ).card ≤ (Nat.properDivisors N).card := by
      exact Finset.card_le_card h_divisors;
    rcases N with ( _ | _ | _ | _ | _ | _ | N ) <;> simp_all +arith +decide;
    · exact absurd h_r ( by native_decide );
    · exact le_trans ( by rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> norm_num <;> omega ) h_card;
  rcases n : c_k 4 N with ( _ | _ | _ | _ | _ | _ | c_k4N ) <;> simp_all ( config := { decide := Bool.true } );
  · norm_num at *;
  · unfold c_k at *;
    rcases x : Finset.sort ( fun x x_1 => x ≤ x_1 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | k ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
    · have := x ▸ Finset.sort_sorted ( · ≤ · ) N.divisors; simp_all ( config := { decide := Bool.true } ) ;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
  · unfold c_k at *;
    rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ ) <;> aesop;
    · have := k ▸ Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
  · unfold c_k at * ; aesop;
    rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    · have := k ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
    · have := k ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
  · -- By simplifying the inequality $1 < 2⁻¹ + 3⁻¹ + (c_k4N + 6)⁻¹$, we can derive a contradiction.
    field_simp at h_r;
    rw [ lt_div_iff₀ ] at h_r <;> linarith

/-
If $c_3(a_n) \\ge 4$, then $R(a_n) < 1$.
-/
lemma lem_decreasing_condition (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → c_k 3 N ≥ 4 → R N < 1 := by
  -- By Lemma~\\ref{lem:ratio_for_even}, $R(N) = \\frac{1}{2} + \\frac{1}{c_3} + \\frac{1}{c_4}$.
  intro h_even h_card h_c3
  have h_ratio : R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
    exact?;
  -- Since $c_k 4 N > c_k 3 N$, we have $c_k 4 N \\geq c_k 3 N + 1$.
  have h_c4 : c_k 4 N ≥ c_k 3 N + 1 := by
    -- Since the list of divisors is sorted in ascending order and there are at least four divisors, the fourth element must be strictly greater than the third.
    have h_sorted : ∀ {l : List ℕ}, List.Sorted (· ≤ ·) l → List.Nodup l → 4 ≤ l.length → l[3]! > l[2]! := by
      aesop;
      rcases l with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | l ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
      · omega;
      · grind;
    have h_sorted : List.Sorted (· ≤ ·) ((Nat.divisors N).sort (· ≤ ·)) ∧ List.Nodup ((Nat.divisors N).sort (· ≤ ·)) ∧ 4 ≤ ((Nat.divisors N).sort (· ≤ ·)).length := by
      rw [ ← Nat.cons_self_properDivisors ] <;> aesop;
    unfold c_k; aesop;
  rw [ h_ratio, div_add_div, div_add_div, div_lt_iff₀ ] <;> norm_cast <;> nlinarith only [ h_c3, h_c4 ]

/-
If an even integer $N$ has $v_3(N)=0$ and $v_3(S(N))>0$, then $c_3(N) \\equiv 2 \\pmod 3$ and $c_4(N) \\equiv 2 \\pmod 3$.
-/
lemma lem_v3_transition_condition (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → c_k 3 N % 3 = 2 ∧ c_k 4 N % 3 = 2 := by
  -- Since $N$ is even and $v_3(N) = 0$, $N$ is not divisible by 3. However, $S(N)$ is divisible by 3 because $v_3(S(N)) > 0$.
  intro h_even h_card h_v3N h_v3SN
  have h_not_div3 : ¬(3 ∣ N) := by
    -- Since the p-adic valuation of 3 for N is zero, 3 does not divide N.
    simp [padicValNat] at h_v3N;
    exact h_v3N ( Nat.pos_of_ne_zero ( by aesop_cat ) );
  -- Since $S(N)$ is divisible by 3, we have $S(N) = N * R(N)$ and $R(N) = \\frac{1}{2} + \\frac{1}{c_3} + \\frac{1}{c_4}$.
  have h_RN_div3 : 3 ∣ (c_k 3 N) * (c_k 4 N) + 2 * (c_k 4 N) + 2 * (c_k 3 N) := by
    have h_RN_div3 : 3 ∣ (N * (c_k 3 N * c_k 4 N + 2 * c_k 4 N + 2 * c_k 3 N)) := by
      have h_RN_div3 : S N = N * (1 / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) : ℚ) := by
        have h_ratio : R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
          exact?;
        rw [ ← h_ratio ];
        unfold R;
        rw [ mul_div_cancel₀ _ ( by aesop ) ];
      have h_RN_div3 : (S N : ℚ) * 2 * (c_k 3 N) * (c_k 4 N) = N * ((c_k 3 N) * (c_k 4 N) + 2 * (c_k 4 N) + 2 * (c_k 3 N)) := by
        by_cases h : c_k 3 N = 0 <;> by_cases h' : c_k 4 N = 0 <;> simp_all ( config := { decide := Bool.true } ) [ -one_div, field_simps ] ; ring;
        · unfold c_k at h;
          rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
          · replace n := congr_arg List.length n; aesop;
          · replace n := congr_arg List.length n; aesop;
            exact absurd n ( Nat.ne_of_gt ( Finset.one_lt_card.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩ ) );
          · have := congr_arg List.length n; norm_num at this;
            exact absurd this ( by linarith [ show Finset.card ( Nat.properDivisors N ) + 1 = Finset.card ( Nat.divisors N ) by rw [ ← Nat.insert_self_properDivisors ] <;> aesop ] );
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
        · unfold c_k at *;
          rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
          · have y := congr_arg List.length x; norm_num at y;
            rw [ ← Nat.cons_self_properDivisors ] at y <;> aesop;
          · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
          · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
        · linear_combination h_RN_div3;
      norm_cast at *;
      exact h_RN_div3 ▸ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by contrapose! h_v3SN; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) _ ) _ ) _;
    exact Or.resolve_left ( Nat.prime_three.dvd_mul.mp h_RN_div3 ) h_not_div3;
  -- Since $c_3$ and $c_4$ are not divisible by 3, their residues modulo 3 must be 1 or 2.
  have h_c3_mod3 : (c_k 3 N) % 3 ≠ 0 := by
    have h_c3_div3 : c_k 3 N ∣ N := by
      unfold c_k;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | h ⟩ ⟩ ⟩ ) <;> aesop;
      · replace x := congr_arg List.length x; aesop;
      · replace x := congr_arg List.length x; aesop;
        exact absurd x ( Nat.ne_of_gt ( Finset.one_lt_card_iff.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩ ) );
      · replace x := congr_arg List.length x; aesop;
        rw [ ← Nat.cons_self_properDivisors ] at x <;> aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x c; aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x c; aesop;
    exact fun h => h_not_div3 <| dvd_trans ( Nat.dvd_of_mod_eq_zero h ) h_c3_div3
  have h_c4_mod3 : (c_k 4 N) % 3 ≠ 0 := by
    intro h; simp_all ( config := { decide := Bool.true } ) [ Nat.dvd_iff_mod_eq_zero ] ;
    simp_all ( config := { decide := Bool.true } ) [ Nat.add_mod, Nat.mul_mod ];
    have := Nat.mod_lt ( c_k 3 N ) three_pos; interval_cases c_k 3 N % 3 <;> contradiction;
  have := Nat.mod_lt ( c_k 3 N ) zero_lt_three; ( have := Nat.mod_lt ( c_k 4 N ) zero_lt_three; interval_cases _ : c_k 3 N % 3 <;> interval_cases _ : c_k 4 N % 3 <;> simp_all ( config := { decide := Bool.true } ) [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod ] ; )

/-
If $a_n$ is a term in an infinite sequence with $c_2=2, c_3=3, c_4=5$, then $a_{n+1}$ is odd.
-/
lemma lem_growth_c4_is_5_impossible (a_n : ℕ) : IsSequence (fun n => if n=0 then a_n else S^[n] a_n) → c_k 2 a_n = 2 → c_k 3 a_n = 3 → c_k 4 a_n = 5 → Odd (S a_n) := by
  aesop;
  -- The conditions $c_2=2, c_3=3, c_4=5$ imply $v_2(a_n)=1, v_3(a_n)\\ge 1, v_5(a_n)\\ge 1$.
  have h_v2 : a_n % 2 = 0 ∧ a_n % 4 ≠ 0 := by
    -- Since $c_k 2 a_n = 2$, we know that $2$ is the second smallest divisor of $a_n$, implying $a_n$ is even.
    have h_even : a_n % 2 = 0 := by
      have := lem_all_terms_even ( fun n => if n = 0 then a_n else S^[n] a_n ) a 0 ; aesop;
      -- Since $a_n$ is even, we have $a_n \\equiv 0 \\pmod{2}$.
      exact Nat.even_iff.mp this;
    unfold c_k at * ; aesop;
    rcases k : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) a_n.divisors ) with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ ) <;> aesop;
    · replace k := congr_arg List.toFinset k ; rw [ Finset.ext_iff ] at k ; have := k 4 ; simp_all ( config := { decide := Bool.true } );
      have := k 1; have := k 2; have := k 3; have := k 4; have := k 5; have := k a; have := k a_n; have := k ( a_n / 4 ) ; have := k ( a_n / 2 ) ; have := k ( a_n / 3 ) ; have := k ( a_n / 5 ) ; norm_num at * ; aesop;
    · have := k ▸ Finset.sort_sorted ( · ≤ · ) a_n.divisors; aesop;
      have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ Nat.dvd_of_mod_eq_zero a_4, by aesop ⟩ ) ; aesop;
      linarith [ left_7 4 h_2 ];
  -- Using Definition~\\ref{def:sequence_function}, $a_{n+1} = a_n R(a_n)$. The exponent of 2 in this result is $v_2(a_{n+1}) = v_2(a_n) + v_2(R(a_n))$.
  have h_exp : S a_n = a_n * (31 / 30 : ℚ) := by
    -- By Lemma~\\ref{lem:ratio_for_even}, $R(a_n) = \\frac{1}{2} + \\frac{1}{3} + \\frac{1}{5} = \\frac{31}{30}$.
    have h_ratio : R a_n = (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 5 := by
      rw [ lem_ratio_for_even ];
      · aesop;
      · exact Nat.even_iff.mpr h_v2.1;
      · have := a.2.1 0; aesop;
    unfold R at h_ratio;
    rw [ div_eq_iff ] at h_ratio <;> first |linarith|aesop;
  -- Since $a_n$ is divisible by 2 but not by 4, we have $v_2(a_n) = 1$. Therefore, $v_2(a_{n+1}) = v_2(a_n) + v_2(31/30) = 1 + 0 - 1 = 0$.
  have h_v2_a_n_plus_1 : (S a_n) % 2 = 1 := by
    rw [ mul_div, eq_div_iff ] at h_exp <;> norm_cast at *;
    grind;
  exact Nat.odd_iff.mpr h_v2_a_n_plus_1

/-
If an even integer $N$ has $v_3(N)=0$ and $v_3(S(N))>0$, then $v_2(N)=1$.
-/
lemma lem_v3_transition_v2_is_1 (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → padicValNat 2 N = 1 := by
  aesop;
  -- If $v_2(N) \\geq 2$, then $4$ is a divisor of $N$. Since $v_3(N) = 0$, $3$ is not a divisor of $N$. Therefore, the smallest divisor of $N$ greater than $2$ is $4$, so $c_3(N) = 4$.
  by_cases h_v2 : padicValNat 2 N ≥ 2;
  · -- Since $v_2(N) \\geq 2$, $4$ is a divisor of $N$. Since $v_3(N) = 0$, $3$ is not a divisor of $N$. Therefore, the smallest divisor of $N$ greater than $2$ is $4$, so $c_3(N) = 4$.
    have h_c3 : c_k 3 N = 4 := by
      -- Since $v_2(N) \\geq 2$, $4$ is a divisor of $N$. Since $v_3(N) = 0$, $3$ is not a divisor of $N$. Therefore, the smallest divisor of $N$ greater than $2$ is $4$, so $c_3(N) = 4$ and $c_4(N) = 5$.
      have h_divisors : (Nat.divisors N).sort (· ≤ ·) = [1, 2, 4] ++ (Nat.divisors N \\ {1, 2, 4}).sort (· ≤ ·) := by
        have h_divisors : (Nat.divisors N).sort (· ≤ ·) = (insert 1 (insert 2 (insert 4 (Nat.divisors N \\ {1, 2, 4})))).sort (· ≤ ·) := by
          congr;
          -- Since $N$ is even and has at least three proper divisors, $1$, $2$, and $4$ are all divisors of $N$.
          have h_divisors : 1 ∈ Nat.divisors N ∧ 2 ∈ Nat.divisors N ∧ 4 ∈ Nat.divisors N := by
            aesop;
            · exact even_iff_two_dvd.mp a;
            · exact dvd_trans ( pow_dvd_pow 2 h_v2 ) ( Nat.ordProj_dvd _ _ );
          ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx4 : x = 4 <;> aesop;
        rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
        all_goals simp_all ( config := { decide := Bool.true } );
        · intro b hb _ hb1 hb2 hb4; contrapose! hb1; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
        · exact fun a ha _ ha1 ha2 ha4 => Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos ha ( Nat.pos_of_ne_zero ‹_› ) ) ( Ne.symm ha1 );
        · exact fun a ha _ _ _ _ => Nat.pos_of_dvd_of_pos ha ( Nat.pos_of_ne_zero ‹_› );
      unfold c_k;
      aesop;
    -- By Lemma~\\ref{lem:v3_transition_condition}, this implies $c_3(N) \\equiv 2 \\pmod 3$.
    have h_c3_mod : c_k 3 N % 3 = 2 := by
      -- Since $c_k 3 N = 4$, we have $4 \\mod 3 = 1$, which contradicts the lemma that $c_k 3 N \\equiv 2 \\pmod{3}$. Therefore, our assumption that $c_k 3 N = 4$ must be incorrect.
      have h_contra : c_k 3 N % 3 = 2 := by
        have h_lemma : padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → c_k 3 N % 3 = 2 := by
          intros; exact lem_v3_transition_condition N a a_1 ‹_› ‹_› |>.1;
        exact h_lemma (by
        exact padicValNat.eq_zero_of_not_dvd h_1) (by
        assumption);
      exact h_contra;
    norm_num [ h_c3 ] at h_c3_mod;
  · interval_cases _ : padicValNat 2 N <;> simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_iff ];
    -- Since $N$ is even, we have $2 \\mid N$, which contradicts $h_1$.
    have h_contra : 2 ∣ N := by
      -- Since $N$ is even, we have $2 \\mid N$ by definition.
      exact even_iff_two_dvd.mp a;
    grind

/-
If $N$ is a fixed point (i.e., $R(N)=1$), then its smallest divisors are $c_2(N)=2, c_3(N)=3, c_4(N)=6$.
-/
lemma lem_fixed_point_divisors (N : ℕ) : S N = N → 3 ≤ (Nat.properDivisors N).card → c_k 2 N = 2 ∧ c_k 3 N = 3 ∧ c_k 4 N = 6 := by
  -- By Lemma~\\ref{lem:ratio_for_even}, this becomes $\\frac{1}{2} + \\frac{1}{c_3} + \\frac{1}{c_4} = 1$, which simplifies to $\\frac{1}{c_3} + \\frac{1}{c_4} = \\frac{1}{2}$.
  intro h_fixed_point h_card
  have h_ratio : (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) = 1 := by
    have h_ratio : R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
      apply lem_ratio_for_even;
      · contrapose! h_fixed_point;
        -- Since $N$ is odd, by Lemma~\\ref{lem:ratio_for_odd}, we have $R(N) < 1$.
        have h_ratio_lt_one : R N < 1 := by
          exact lem_ratio_for_odd N ( by simpa using h_fixed_point ) h_card;
        unfold R at h_ratio_lt_one;
        rw [ div_lt_one ] at h_ratio_lt_one <;> norm_cast at * ; aesop;
        exact Nat.pos_of_ne_zero ( by rintro rfl; contradiction );
      · assumption;
    rw [ ← h_ratio, show R N = 1 from by rw [ show R N = ( S N : ℚ ) / N by exact rfl ] ; rw [ h_fixed_point, div_self ] ; aesop ];
  have h_c3 : c_k 3 N = 3 := by
    -- Since $c_3 < c_4$, we have $\\frac{1}{c_3} > \\frac{1}{c_4}$, so $\\frac{2}{c_3} > \\frac{1}{c_3} + \\frac{1}{c_4} = \\frac{1}{2}$, which implies $c_3 < 4$.
    have h_c3_lt_4 : c_k 3 N < 4 := by
      contrapose h_ratio;
      -- Since $c_k 3 N \\geq 4$, we have $c_k 4 N \\geq c_k 3 N + 1$.
      have h_c4_ge_c3_plus_1 : c_k 4 N ≥ c_k 3 N + 1 := by
        -- Since the divisors are sorted in ascending order and distinct, the fourth divisor must be greater than the third.
        have h_sorted : ∀ {l : List ℕ}, List.Sorted (· ≤ ·) l → List.Nodup l → ∀ i j : ℕ, i < j → i < List.length l → j < List.length l → l.get! i < l.get! j := by
          intros l hl_sorted hl_nodup i j hij hi hj;
          field_simp;
          have := List.pairwise_iff_get.mp hl_sorted;
          exact lt_of_le_of_ne ( this ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij ) fun h => by have := List.nodup_iff_injective_get.mp hl_nodup; have := @this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
        have h_sorted_divisors : List.Sorted (· ≤ ·) ((Nat.divisors N).sort (· ≤ ·)) ∧ List.Nodup ((Nat.divisors N).sort (· ≤ ·)) := by
          exact ⟨ Finset.sort_sorted _ _, Finset.sort_nodup _ _ ⟩;
        have := @h_sorted _ h_sorted_divisors.left h_sorted_divisors.right 2 3 ( by decide ) ?_ ?_ <;> aesop;
        · unfold c_k; aesop;
        · rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
          linarith;
        · rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
          linarith;
      rw [ div_add_div, div_add_div, div_eq_iff ] <;> norm_cast <;> nlinarith only [ h_ratio, h_c4_ge_c3_plus_1 ];
    interval_cases _ : c_k 3 N <;> simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
      replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
    · linarith [ inv_pos.mpr ( show 0 < ( c_k 4 N : ℚ ) by norm_cast; contrapose! h_ratio; aesop ) ];
    · norm_num at h_ratio;
      unfold c_k at *;
      rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | ⟨ g, _ | h ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ <;> aesop;
      all_goals replace := Finset.sort_sorted ( fun x1 x2 => x1 ≤ x2 ) N.divisors; simp_all ( config := { decide := Bool.true } );
      have := congr_arg List.length n; norm_num at this;
      rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
  aesop;
  · unfold c_k at *;
    rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ ; aesop;
    · aesop;
    · have := congr_arg List.length n; norm_num at this;
      rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
    · aesop;
      norm_num at h_ratio;
    · have := Finset.sort_sorted ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
      -- Since $a \\leq b \\leq 3$ and $a \\leq d$, and the list is sorted, we deduce that $a = 1$ and $b = 2$.
      have ha : a = 1 := by
        interval_cases a <;> simp_all ( config := { decide := Bool.true } );
        · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
        · have := Nat.mem_divisors_self N ( by aesop_cat ) ; replace n := congr_arg List.toFinset n ; rw [ Finset.ext_iff ] at n ; specialize n 1 ; aesop;
        · interval_cases b ; norm_num at *;
          have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
          have := this 1; aesop;
          linarith [ this.mp ( by rintro rfl; contradiction ) ];
      interval_cases b <;> simp_all ( config := { decide := Bool.true } );
      · have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
      · have := n ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      interval_cases b <;> interval_cases a <;> norm_num at *;
      all_goals have := n ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) N.divisors; simp_all ( config := { decide := Bool.true } ) ;
      replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
  · exact_mod_cast ( by nlinarith [ inv_mul_cancel₀ ( show ( c_k 4 N : ℚ ) ≠ 0 from fun h => by norm_num [ h ] at h_ratio ) ] : ( c_k 4 N : ℚ ) = 6 )

/-
An integer $N$ is a fixed point if and only if $N$ is of the form $6m$ for some positive integer $m$ with $\\gcd(m,10)=1$.
-/
lemma lem_fixed_point_form (N : ℕ) : (S N = N ∧ 3 ≤ (Nat.properDivisors N).card) ↔ ∃ m, 0 < m ∧ Nat.Coprime m 10 ∧ N = 6 * m := by
  constructor;
  · intro h;
    -- By Lemma~\\ref{lem:fixed_point_divisors}, its smallest divisors are $c_2(N)=2$, $c_3(N)=3$, and $c_4(N)=6$.
    have h_divisors : c_k 2 N = 2 ∧ c_k 3 N = 3 ∧ c_k 4 N = 6 := by
      -- By Lemma~\\ref{lem:fixed_point_divisors}, if $S(N) = N$ and $N$ has at least three proper divisors, then the smallest divisors of $N$ are $2$, $3$, and $6$.
      apply lem_fixed_point_divisors; exact h.left; exact h.right;
    -- This requires that $N$ be divisible by 6, not divisible by 4, and not divisible by 5.
    have h_div_conditions : 6 ∣ N ∧ ¬(4 ∣ N) ∧ ¬(5 ∣ N) := by
      have := lem_structure_of_fixed_points N;
      rcases N with ( _ | _ | N ) <;> simp_all +arith +decide;
      exact this ( by rw [ ← Nat.cons_self_properDivisors ] <;> aesop );
    rcases h_div_conditions.1 with ⟨ m, rfl ⟩;
    exact ⟨ m, Nat.pos_of_ne_zero ( by aesop_cat ), Nat.Coprime.symm <| Nat.Coprime.gcd_eq_one <| Nat.Coprime.mul ( show Nat.Coprime 2 m from Nat.prime_two.coprime_iff_not_dvd.2 fun contra => h_div_conditions.2.1 <| dvd_trans ( by decide ) ( mul_dvd_mul_left _ contra ) ) ( show Nat.Coprime 5 m from Nat.Prime.coprime_iff_not_dvd ( by decide ) |>.2 fun contra => h_div_conditions.2.2 <| dvd_trans ( by decide ) ( mul_dvd_mul_left _ contra ) ), rfl ⟩;
  · bound;
    · -- The three largest proper divisors of $6w$ are $3w$, $2w$, and $w$. Their sum is $3w + 2w + w = 6w$.
      have h_divisors : (Nat.properDivisors (6 * w)).sort (· ≥ ·) = [3 * w, 2 * w, w] ++ (Nat.properDivisors (6 * w) \\ {3 * w, 2 * w, w}).sort (· ≥ ·) := by
        norm_num +zetaDelta at *;
        rw [ ← Finset.sort_insert ];
        · rw [ ← Finset.sort_insert ];
          · rw [ ← Finset.sort_insert ];
            · congr with x ; aesop;
              · grind;
              · exact ⟨ 2, by ring ⟩;
              · exact ⟨ 3, by ring ⟩;
            · aesop;
              obtain ⟨ k, hk ⟩ := left_2;
              rcases k with ( _ | _ | _ | _ | _ | k ) <;> nlinarith;
            · aesop;
              linarith;
          · aesop;
            obtain ⟨ k, hk ⟩ := left_2;
            rcases k with ( _ | _ | _ | _ | _ | k ) <;> simp_all! +arith +decide;
            · omega;
            · omega;
            · omega;
            · nlinarith;
          · aesop;
            linarith;
        · aesop;
          obtain ⟨ k, hk ⟩ := left_2;
          rcases k with ( _ | _ | _ | _ | _ | k ) <;> simp_all! +arith +decide;
          · omega;
          · omega;
          · exact absurd ( Nat.dvd_gcd ( show 2 ∣ w by omega ) ( show 2 ∣ 10 by decide ) ) ( by norm_num [ left_1 ] );
          · rcases k with ( _ | _ | k ) <;> try nlinarith;
            exact absurd ( Nat.dvd_gcd ( show 5 ∣ w by omega ) ( show 5 ∣ 10 by norm_num ) ) ( by aesop );
        · aesop;
      unfold S;
      simp +arith +decide [ h_divisors ];
    · -- Since $w$ is coprime to 10, the proper divisors of $6w$ include at least $1$, $2$, and $3$.
      have h_divisors : Nat.properDivisors (6 * w) ⊇ {1, 2, 3} := by
        simp ( config := { decide := Bool.true } ) [ Finset.insert_subset_iff ];
        -- Since $w$ is a positive integer, $6w$ is clearly greater than $1$, $2$, and $3$.
        have h_ineq : 1 < 6 * w ∧ 2 < 6 * w ∧ 3 < 6 * w := by
          exact ⟨ by linarith, by linarith, by linarith ⟩;
        exact ⟨ h_ineq.1, ⟨ ⟨ 3 * w, by ring ⟩, h_ineq.2.1 ⟩, ⟨ ⟨ 2 * w, by ring ⟩, h_ineq.2.2 ⟩ ⟩;
      exact Finset.card_mono h_divisors

/-
Any integer $N$ of the form $6 \\cdot 12^a \\cdot m$ with $a \\ge 0$ and $\\gcd(m,10)=1$ is a valid starting term $a_1$.
-/
lemma lem_verification_of_form :
  { n | ∃ a m, m > 0 ∧ Nat.Coprime m 10 ∧ n = 6 * 12 ^ a * m } ⊆ { a₁ | ∃ a : ℕ → ℕ, IsSequence a ∧ a₁ = a 0 } := by
    -- From Lemma 2, we know that if $a_1 = 6 \\cdot 12^a \\cdot m$, then $a_{n+1} = \\frac{13}{12} a_n$ for $n \\leq a$.
    have h_step : ∀ a m : ℕ, 0 < m → Nat.Coprime m 10 → IsSequence (fun n => if n ≤ a then 6 * 12 ^ (a - n) * m * 13 ^ n else 6 * m * 13 ^ a) := by
      intros a m hm h_coprime;
      constructor;
      · aesop;
      · constructor;
        · intro n;
          norm_num +zetaDelta at *;
          split_ifs;
          · refine' Finset.two_lt_card.mpr _;
            simp;
            exact ⟨ 1, ⟨ one_dvd _, by nlinarith [ show 12 ^ ( a - n ) * m * 13 ^ n > 0 by positivity ] ⟩, 2, ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by norm_num ) _ ) _ ) _, by nlinarith [ show 12 ^ ( a - n ) * m * 13 ^ n > 0 by positivity ] ⟩, 3, ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by norm_num ) _ ) _ ) _, by nlinarith [ show 12 ^ ( a - n ) * m * 13 ^ n > 0 by positivity ] ⟩, by norm_num, by norm_num, by norm_num ⟩;
          · refine' le_trans _ ( Finset.card_mono <| show Nat.properDivisors ( 6 * m * 13 ^ a ) ≥ { 1, 2, 3 } from _ );
            · native_decide +revert;
            · norm_num [ Finset.insert_subset_iff ];
              exact ⟨ by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ], ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩, dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩;
        · aesop;
          · rw [ show a - n = ( a - ( n + 1 ) ) + 1 by omega ] ; ring;
            unfold S;
            -- The largest proper divisors of $m \\cdot 12^{a-(1+n)} \\cdot 13^n \\cdot 72$ are $m \\cdot 12^{a-(1+n)} \\cdot 13^n \\cdot 36$, $m \\cdot 12^{a-(1+n)} \\cdot 13^n \\cdot 24$, and $m \\cdot 12^{a-(1+n)} \\cdot 13^n \\cdot 18$.
            have h_divisors : (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)).sort (· ≥ ·) = [m * 12 ^ (a - (1 + n)) * 13 ^ n * 36, m * 12 ^ (a - (1 + n)) * 13 ^ n * 24, m * 12 ^ (a - (1 + n)) * 13 ^ n * 18] ++ (Finset.sort (· ≥ ·) (Finset.filter (fun d => d < m * 12 ^ (a - (1 + n)) * 13 ^ n * 18) (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)))) := by
              have h_divisors : (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)).sort (· ≥ ·) = (insert (m * 12 ^ (a - (1 + n)) * 13 ^ n * 36) (insert (m * 12 ^ (a - (1 + n)) * 13 ^ n * 24) (insert (m * 12 ^ (a - (1 + n)) * 13 ^ n * 18) (Finset.filter (fun d => d < m * 12 ^ (a - (1 + n)) * 13 ^ n * 18) (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)))))).sort (· ≥ ·) := by
                congr;
                ext; aesop;
                · rcases left with ⟨ k, hk ⟩;
                  rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> norm_num at * <;> first | exact Or.inl <| by nlinarith | exact Or.inr <| Or.inl <| by nlinarith | exact Or.inr <| Or.inr <| Or.inl <| by nlinarith | exact Or.inr <| Or.inr <| Or.inr <| by nlinarith;
                · exact ⟨ 2, by ring ⟩;
                · exact mul_dvd_mul_left _ ( by decide );
                · exact mul_dvd_mul_left _ ( by decide );
              rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
              all_goals simp +arith +decide;
              · intros; linarith;
              · intros; linarith;
              · linarith;
              · intros; linarith;
              · linarith;
            aesop;
            ring;
          · linarith;
          · cases h_1.eq_or_lt <;> first | linarith | aesop;
            -- By definition of $S$, we know that $S(6 \\cdot m \\cdot 13^n) = 6 \\cdot m \\cdot 13^n$ since $6 \\cdot m \\cdot 13^n$ is a fixed point.
            have h_fixed_point : S (6 * m * 13 ^ n) = 6 * m * 13 ^ n := by
              have h_fixed_point : ∀ m : ℕ, 0 < m → Nat.Coprime m 10 → S (6 * m) = 6 * m := by
                exact fun m hm h_coprime => lem_fixed_point_form ( 6 * m ) |>.2 ⟨ m, hm, h_coprime, rfl ⟩ |>.1;
              simpa only [ mul_assoc ] using h_fixed_point ( m * 13 ^ n ) ( by positivity ) ( by exact Nat.Coprime.mul h_coprime ( by cases n <;> norm_num ) );
            exact h_fixed_point.symm;
          · -- By definition of $S$, we know that $S(6 * m * 13^a) = 6 * m * 13^a$ since $6 * m * 13^a$ is a fixed point.
            have h_fixed_point : S (6 * m * 13 ^ a) = 6 * m * 13 ^ a := by
              have h_form : ∃ m', 0 < m' ∧ Nat.Coprime m' 10 ∧ 6 * m * 13 ^ a = 6 * m' := by
                exact ⟨ m * 13 ^ a, by positivity, by exact Nat.Coprime.mul h_coprime ( by exact Nat.Coprime.pow_left _ ( by decide ) ), by ring ⟩
              aesop;
              exact lem_fixed_point_form _ |>.2 ⟨ w, left, left_1, rfl ⟩ |>.1;
            exact h_fixed_point.symm;
    rintro _ ⟨ a, m, hm, hm', rfl ⟩;
    exact ⟨ _, h_step a m hm hm', by simp ( config := { decide := Bool.true } ) ⟩

/-
If an even integer $N$ has $v_2(N)=1$, $v_3(N)=0$, and $v_3(S(N))>0$, then its divisors $c_3(N)$ and $c_4(N)$ are both odd.
-/
lemma lem_v3_transition_c3_c4_are_odd (N : ℕ) : padicValNat 2 N = 1 → padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → 3 ≤ (Nat.properDivisors N).card → Odd (c_k 3 N) ∧ Odd (c_k 4 N) := by
  intro h2 h3 h4 h5;
  -- Since $c_k 3 N$ and $c_k 4 N$ are both $\\equiv 2 \\pmod 3$, they must be odd.
  have h_odd_c3 : Odd (c_k 3 N) := by
    -- Since $v_2(N)=1$, $N$ is divisible by 2 but not by 4. Thus, the smallest divisor greater than 2 must be odd.
    have h_c3_odd : c_k 3 N ∉ ({1, 2} : Finset ℕ) := by
      unfold c_k; aesop;
      · rcases n : Finset.sort ( · ≤ · ) N.divisors with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
        · replace n := congr_arg List.length n ; simp_all +arith +decide;
          rw [ ← Nat.cons_self_properDivisors ] at n <;> aesop;
        · have := Finset.sort_sorted ( · ≤ · ) N.divisors; simp_all ( config := { decide := Bool.true } ) ;
          rcases x with ( _ | _ | x ) <;> rcases y with ( _ | _ | y ) <;> simp_all +arith +decide;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
          · have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
      · rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | h ⟩ ⟩ ⟩ ) <;> aesop;
        · have := congr_arg List.length n; norm_num at this;
          rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
        · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
          interval_cases x <;> interval_cases y <;> simp_all ( config := { decide := Bool.true } );
          all_goals have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; simp_all ( config := { decide := Bool.true } );
          replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
    rcases k : ( Nat.divisors N |> Finset.sort ( · ≤ · ) ) with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ ) <;> aesop;
    · replace k := congr_arg List.length k; aesop;
    · replace k := congr_arg List.length k; aesop;
      exact absurd k ( by exact Nat.ne_of_gt ( Finset.one_lt_card_iff.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩ ) );
    · replace k := congr_arg List.length k; aesop;
      rw [ ← Nat.cons_self_properDivisors ] at k <;> aesop;
    · have := congr_arg List.length k; norm_num at this;
      rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
    · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors N ) ; aesop;
      unfold c_k at *;
      have := k ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors N ) ; simp_all +arith +decide;
      have ha : a = 1 := by
        have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.one_mem_divisors.2 <| by aesop_cat ) ; aesop;
        · interval_cases a <;> aesop;
          replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
        · interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all ( config := { decide := Bool.true } ) only;
        · grind;
      have hb : b = 2 := by
        have hb : b ≤ 2 := by
          have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ show 2 ∣ N from ?_, by aesop ⟩ ) ; aesop;
          · exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] );
          · aesop;
        interval_cases b <;> simp_all ( config := { decide := Bool.true } );
      have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ Nat.dvd_of_mem_divisors ( show c ∈ Nat.divisors N from by { replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k c; aesop } ), by { aesop } ⟩ ) ; aesop;
      contrapose! right_8;
      have h_even_divisor : c / 2 ∈ Nat.divisors N := by
        have h_even_divisor : c / 2 ∣ N := by
          exact Nat.dvd_trans ( Nat.div_dvd_of_dvd <| even_iff_two_dvd.mp <| by simpa using right_8 ) <| Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| k.symm ▸ by simp ( config := { decide := Bool.true } ) ;
        aesop;
      have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 h_even_divisor; aesop;
      · have := Nat.div_mul_cancel ( even_iff_two_dvd.mp right_8 ) ; aesop;
      · have := Nat.div_mul_cancel ( even_iff_two_dvd.mp right_8 ) ; aesop;
        replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 4; aesop;
        rw [ padicValNat ] at h2 ; aesop;
        simp_all ( config := { decide := Bool.true } ) [ Nat.find_eq_iff ];
      · linarith [ Nat.div_mul_cancel ( even_iff_two_dvd.mp right_8 ) ];
      · omega;
      · grind
  have h_odd_c4 : Odd (c_k 4 N) := by
    -- By Lemma~\\ref{lem:v3_transition_condition}, $c_3 \\equiv 2 \\pmod 3$ and $c_4 \\equiv 2 \\pmod 3$.
    have h_c3_c4_mod3 : c_k 3 N % 3 = 2 ∧ c_k 4 N % 3 = 2 := by
      apply_rules [ lem_v3_transition_condition ];
      exact even_iff_two_dvd.mpr ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] );
    unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
      -- Since $N$ is even, $2$ is a divisor of $N$. The divisors of $N$ in ascending order are $1, 2, c, d$. Since $c$ is the smallest odd divisor greater than $2$, $d$ must be greater than $c$ and cannot be $4$ (as $4$ would imply $v_2(N) \\geq 2$, contradicting $v_2(N) = 1$). Therefore, $d$ must be odd.
      have h_d_odd : d > c ∧ ¬(4 ∣ N) := by
        have h_d_odd : d > c := by
          have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
          cases lt_or_eq_of_le right_1 <;> aesop;
          have := Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
        rw [ padicValNat ] at h2 ; aesop;
        simp_all ( config := { decide := Bool.true } ) [ Nat.find_eq_iff ];
      cases this 1 ; cases this 2 ; cases this c ; cases this d ; aesop;
      · have := this 2; norm_num at this;
        cases this.mp ( dvd_trans ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( show N % 2 = 0 from Nat.mod_eq_zero_of_dvd <| by exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) ) ) ) <;> aesop;
        · have := this_1 d; specialize this_1 ( d / 2 ) ; rcases Nat.even_or_odd' d with ⟨ k, rfl | rfl ⟩ <;> simp_all +arith +decide;
          rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
          · interval_cases c <;> trivial;
          · exact absurd ( this_1.mp ( dvd_of_mul_left_dvd this ) ) ( by omega );
        · contradiction;
        · interval_cases c <;> trivial;
      · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
        interval_cases a <;> simp_all ( config := { decide := Bool.true } );
        · specialize this_1 0 ; aesop;
        · have := this_1 2; norm_num at this;
          cases this.mp ( dvd_trans ( by decide ) ( Nat.dvd_of_mod_eq_zero ( show N % 2 = 0 from Nat.mod_eq_zero_of_dvd <| by exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) ) ) ) <;> aesop;
          · contradiction;
          · interval_cases c ; trivial;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      -- Since $d$ is a divisor of $N$ and $N$ is even, but $c_k 3 N = 2$ (the smallest even divisor), $d$ must be odd.
      have h_d_odd : ¬(2 ∣ d) := by
        contrapose! left_4;
        cases left_4 ; aesop;
        have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
        -- Since $c$ is the third smallest divisor and $N$ is even, $c$ must be greater than 2.
        have hc_gt_2 : 2 < c := by
          -- Since $c$ is a divisor of $N$ and $N$ is even, $c$ must be greater than 2.
          have hc_gt_2 : c ≠ 2 := by
            simp +zetaDelta at *;
            exact fun h => by simp_all ( config := { decide := Bool.true } ) [ Nat.even_iff ] ;
          exact lt_of_le_of_ne ( Nat.le_of_not_lt fun h => by interval_cases c <;> simp_all ( config := { decide := Bool.true } ) ) ( Ne.symm hc_gt_2 );
        -- Since $a \\leq b \\leq c$ and $a \\neq b$, we have $b \\geq a + 1$. Similarly, since $b \\leq c$ and $b \\neq c$, we have $c \\geq b + 1$. Therefore, $c \\geq a + 2$.
        have hc_ge_a2 : c ≥ a + 2 := by
          omega;
        have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
        have := this 2; norm_num at this;
        cases this.mp ⟨ by exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.dvd_iff_mod_eq_zero ] ; exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) ), by aesop ⟩ <;> aesop;
        · cases this_1 ( 1 : ℕ ) ; aesop;
          grind;
        · interval_cases a <;> simp_all ( config := { decide := Bool.true } );
          · specialize this_1 0 ; aesop;
          · have := this_1 ( 2 * w ) ; specialize this_1 w ; aesop;
            rcases w with ( _ | _ | w ) <;> simp_all +arith +decide;
            -- Since $w + 2$ divides $N$ and $w + 2 \\notin \\text{tail}$, we must have $w = 0$ or $w + 2 = c$ or $w + 2 = k$.
            have h_w_cases : w = 0 ∨ w + 2 = c ∨ w + 2 = k := by
              -- Since $w + 2$ divides $N$ and $w + 2 \\notin \\text{tail}$, we must have $w = 0$ or $w + 2 = c$ or $w + 2 = k$ by the hypothesis \`this_1\`.
              have h_w_cases : w = 0 ∨ w + 2 = c ∨ w + 2 = k ∨ w + 2 ∈ tail := by
                exact this_1.mp ( dvd_of_mul_left_dvd left_1 );
              grind;
            rcases h_w_cases with ( rfl | h_w_cases | h_w_cases ) <;> simp_all +arith +decide;
            · omega;
            · bound;
        · linarith;
        · grind;
      norm_num +zetaDelta at *;
      exact Nat.odd_iff.mpr h_d_odd
  exact ⟨h_odd_c3, h_odd_c4⟩

/-
If $N$ is an even integer with $v_3(N)=0$ such that $S(N)$ is divisible by 3, then $S(N)$ is odd.
-/
lemma lem_transition_to_v3_positive_is_odd (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → padicValNat 3 N = 0 → 3 ∣ S N → Odd (S N) := by
  -- By Lemma~\\ref{lem:v3_transition_v2_is_1}, the hypotheses imply $v_2(N)=1$.
  intro h_even h_card h_v3 h_div3
  have h_v2 : padicValNat 2 N = 1 := by
    apply_rules [ lem_v3_transition_v2_is_1 ];
    contrapose! h_v3; aesop;
    unfold S at h_v3;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
    · replace x := congr_arg List.length x; aesop;
      interval_cases N <;> trivial;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
  -- Since $c_3(N)$ and $c_4(N)$ are divisible by 3, we have $c_3(N) = 4$ or $c_3(N) = 5$.
  have h_c3 : Odd (c_k 3 N) ∧ Odd (c_k 4 N) := by
    apply_rules [ lem_v3_transition_c3_c4_are_odd ];
    unfold padicValNat; aesop;
    unfold S at h;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · replace x := congr_arg List.length x; aesop;
      interval_cases N <;> trivial;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
  -- By definition of $S$, we know that $S(N) = \\frac{N}{c_2} + \\frac{N}{c_3} + \\frac{N}{c_4}$.
  have h_S_def : S N = N / c_k 2 N + N / c_k 3 N + N / c_k 4 N := by
    unfold S;
    -- The three largest proper divisors of $N$ are $N/2$, $N/3$, and $N/4$.
    have h_largest_divisors : (Nat.properDivisors N).sort (· ≥ ·) = (List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·))).drop 1 := by
      have h_largest_divisors : List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·)) = N.divisors.sort (· ≥ ·) := by
        have h_largest_divisors : List.Perm (List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·))) (Finset.sort (· ≥ ·) (Nat.divisors N)) := by
          rw [ List.perm_iff_count ];
          intro a; rw [ List.count_eq_of_nodup, List.count_eq_of_nodup ];
          · simp;
            bound;
            · exact False.elim <| h ⟨ Nat.div_dvd_of_dvd left_1, right_2 ⟩;
            · exact False.elim <| h ⟨ N / a, ⟨ Nat.div_dvd_of_dvd left_1, right_1 ⟩, by rw [ Nat.div_div_self ] <;> aesop ⟩;
          · exact Finset.sort_nodup _ _;
          · rw [ List.nodup_map_iff_inj_on ];
            · aesop;
              exact?;
            · exact Finset.sort_nodup _ _;
        have h_sorted : List.Sorted (· ≥ ·) (List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·))) := by
          have h_sorted : ∀ {l : List ℕ}, List.Sorted (· ≤ ·) l → (∀ d ∈ l, d ∣ N) → List.Sorted (· ≥ ·) (List.map (fun d => N / d) l) := by
            intros l hl_sorted hl_div; induction hl_sorted <;> aesop;
            exact Nat.div_le_div_left ( a_1 _ a_4 ) ( Nat.pos_of_dvd_of_pos left_1 ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
          exact h_sorted ( Finset.sort_sorted ( · ≤ · ) _ ) fun x hx => Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 hx;
        exact List.eq_of_perm_of_sorted h_largest_divisors h_sorted ( Finset.sort_sorted ( fun x1 x2 => x1 ≥ x2 ) _ );
      have h_largest_divisors : N.divisors.sort (· ≥ ·) = N :: N.properDivisors.sort (· ≥ ·) := by
        rw [ ← Nat.cons_self_properDivisors ];
        · rw [ Finset.sort_cons ];
          exact fun x hx => Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.mem_properDivisors.mp hx |>.1 );
        · aesop;
      aesop;
    unfold c_k; aesop;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
  -- Since $c_k 2 N = 2$, we have $N / c_k 2 N = N / 2$, which is odd because $N$ is even and $v2(N) = 1$.
  have h_N_div_2_odd : Odd (N / c_k 2 N) := by
    have h_c2 : c_k 2 N = 2 := by
      -- Since $N$ is even, its smallest divisor greater than 1 is 2.
      have h_divisors_order : (Nat.divisors N).sort (· ≤ ·) = 1 :: 2 :: (Nat.divisors N \\ {1, 2}).sort (· ≤ ·) := by
        rw [ ← Finset.sort_insert ];
        · rw [ ← Finset.sort_insert ];
          · congr;
            ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> aesop;
            exact even_iff_two_dvd.mp h_even;
          · aesop;
            exact Nat.pos_of_dvd_of_pos left_1 ( Nat.pos_of_ne_zero right_2 );
          · aesop;
        · exact fun x hx => Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩;
        · aesop;
      unfold c_k; aesop;
    rw [ padicValNat ] at h_v2;
    split_ifs at h_v2 ; simp_all ( config := { decide := Bool.true } ) [ Nat.find_eq_iff ];
    exact Nat.odd_iff.mpr ( by omega );
  have := Nat.div_mul_cancel ( show c_k 3 N ∣ N from Nat.dvd_of_mem_divisors <| by
    unfold c_k at *;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x c; aesop; ) ; have := Nat.div_mul_cancel ( show c_k 4 N ∣ N from Nat.dvd_of_mem_divisors <| by
    -- Since $c_k 4 N$ is the fourth smallest divisor of $N$, it must be a divisor of $N$.
    have h_c4_div : c_k 4 N ∈ (Nat.divisors N).sort (· ≤ ·) := by
      unfold c_k;
      -- Since the list is sorted in ascending order, the fourth element is indeed a divisor of N.
      have h_div : (Finset.sort (· ≤ ·) (Nat.divisors N)).length ≥ 4 := by
        rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
      rcases n : Finset.sort ( · ≤ · ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 h_c4_div ) ; replace := congr_arg Even this; simp_all ( config := { decide := Bool.true } ) [ parity_simps ] ;
  aesop;
  · replace this_1 := congr_arg Even this_1; simp_all ( config := { decide := Bool.true } ) [ parity_simps ] ;
    exact this_1.resolve_right ( by simpa using left );
  · exact absurd h_2 ( by simpa using right );
  · exact absurd h_2 ( by simpa using right )

/-
An infinite sequence cannot have a term $a_k$ with $v_3(a_k)=0$.
-/
lemma lem_no_v3_zero_terms (a : ℕ → ℕ) : IsSequence a → ∀ k, padicValNat 3 (a k) ≠ 0 := by
  intros ha k;
  by_contra h_contra;
  -- If for all $n \\geq k$, $v_3(a_n) = 0$, then the subsequence $(a_n)_{n \\geq k}$ would be strictly decreasing, which contradicts the sequence being infinite.
  by_cases h_all_zero : ∀ n ≥ k, padicValNat 3 (a n) = 0;
  · have h_decreasing : ∀ n ≥ k, a (n + 1) < a n := by
      intros n hn;
      have h_decreasing : ∀ n ≥ k, R (a n) < 1 := by
        intros n hn;
        apply lem_decreasing_condition;
        · exact?;
        · exact ha.2.1 n;
        · by_contra h_contra;
          interval_cases _ : c_k 3 ( a n ) <;> simp_all ( config := { decide := Bool.true } );
          · unfold c_k at *;
            rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | h ⟩ ⟩ ⟩ <;> aesop;
            · replace x := congr_arg List.length x ; aesop;
              exact absurd x ( ne_of_gt ( ha.1 n ) );
            · have := congr_arg List.length x; norm_num at this;
              have := ha.2.1 n;
              rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
              interval_cases a n <;> contradiction;
            · have := congr_arg List.length x; norm_num at this;
              -- Since $a_n$ has at least three proper divisors, the cardinality of its divisors must be at least 3. This contradicts the assumption that it's 2.
              have h_card : 3 ≤ (Nat.divisors (a n)).card := by
                have := ha.2.1 n;
                exact le_trans this ( Finset.card_mono <| fun x hx => Nat.mem_divisors.mpr ⟨ Nat.mem_properDivisors.mp hx |>.1, by specialize ha; have := ha.1 n; aesop ⟩ );
              linarith;
            · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
            · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
          · unfold c_k at *;
            rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> aesop;
            · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              interval_cases y <;> interval_cases x_1 <;> have := ha.2.1 n <;> simp_all ( config := { decide := Bool.true } );
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x ( a n ) ; aesop;
                by_cases h : a n = 0 <;> aesop;
            · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              interval_cases x_1 <;> interval_cases y <;> simp_all ( config := { decide := Bool.true } );
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
              · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
          · unfold c_k at *;
            rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> aesop;
            · have := congr_arg List.length x; norm_num at this;
              -- This contradicts the assumption that the number of proper divisors is at least 3.
              have h_contra : (Nat.divisors (a n)).card ≥ 4 := by
                have := ha.2.1 n;
                rw [ ← Nat.cons_self_properDivisors ] <;> aesop;
              linarith;
            · have h_divisors : x_1 = 1 := by
                have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
                interval_cases x_1 <;> simp_all ( config := { decide := Bool.true } );
                · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
                · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              interval_cases y <;> simp_all ( config := { decide := Bool.true } );
              · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              · have := x ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) ; aesop;
          · -- Since $c_k 3 (a n) = 3$, it follows that $3$ divides $a n$.
            have h_div : 3 ∣ a n := by
              unfold c_k at *;
              rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | h ⟩ ⟩ ⟩ ) <;> aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 3; aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 3; aesop;
            cases h_all_zero n hn <;> aesop;
            exact absurd h ( ne_of_gt ( ha.1 n ) );
      have := h_decreasing n hn;
      unfold R at this;
      rw [ div_lt_one ] at this <;> norm_cast at * <;> have := ha.2.2 n <;> aesop;
      exact ha.1 n;
    -- Since the subsequence $(a_n)_{n \\geq k}$ is strictly decreasing and consists of positive integers, it must be finite.
    have h_finite : Set.Finite (Set.range (fun n => a (k + n))) := by
      exact Set.finite_iff_bddAbove.mpr ⟨ a k, by rintro x ⟨ n, rfl ⟩ ; exact Nat.recOn n ( by norm_num ) fun n ihn => by linarith! [ h_decreasing ( k + n ) ( by linarith ) ] ⟩;
    exact h_finite.not_infinite <| Set.infinite_range_of_injective ( StrictAnti.injective <| strictAnti_nat_of_succ_lt fun n => h_decreasing _ <| Nat.le_add_right _ _ );
  · -- Therefore, there must be a first term $a_m$ with $m > k$ such that $v_3(a_m) > 0$.
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m > k, padicValNat 3 (a m) > 0 ∧ ∀ n, k < n ∧ n < m → padicValNat 3 (a n) = 0 := by
      obtain ⟨m, hm₁, hm₂⟩ : ∃ m > k, padicValNat 3 (a m) > 0 := by
        push_neg at h_all_zero;
        exact h_all_zero.imp fun n hn => ⟨ lt_of_le_of_ne hn.1 ( by aesop ), Nat.pos_of_ne_zero hn.2 ⟩;
      exact ⟨ Nat.find ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m > k, padicValNat 3 ( a m ) > 0 ), Nat.find_spec ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m > k, padicValNat 3 ( a m ) > 0 ) |>.1, Nat.find_spec ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m > k, padicValNat 3 ( a m ) > 0 ) |>.2, by aesop ⟩;
    -- Since $a_m = S(a_{m-1})$ and $v_3(a_{m-1}) = 0$, by Lemma~\\ref{lem:transition_to_v3_positive_is_odd}, $a_m$ must be odd.
    have h_odd_am : Odd (a m) := by
      have h_odd_am : padicValNat 3 (a (m - 1)) = 0 ∧ 3 ∣ a m := by
        rcases m <;> aesop;
        · cases ha ; aesop;
          linarith [ left_3 k ];
        · exact absurd h ( ne_of_gt ( ha.1 k ) );
        · cases lt_or_eq_of_le ( Nat.le_of_lt_succ hm₁ ) <;> aesop;
        · exact?;
      have h_odd_am : Odd (S (a (m - 1))) := by
        apply lem_transition_to_v3_positive_is_odd;
        · exact?;
        · exact ha.2.1 ( m - 1 );
        · exact h_odd_am.left;
        · have := ha.2.2 ( m - 1 ) ; rcases m <;> aesop;
      have := ha.2.2 ( m - 1 ) ; rcases m <;> aesop;
    -- This contradicts Lemma~\\ref{lem:no_odd_terms}, which states that no term in the sequence can be odd.
    have h_contradiction : ∀ n, Even (a n) := by
      exact?;
    exact Nat.not_even_iff_odd.mpr h_odd_am ( h_contradiction m )

/-
For any term $a_n$ in an infinite sequence, it must be divisible by 3. This implies $c_3(a_n)=3$.
-/
lemma lem_all_terms_divisible_by_3 (a : ℕ → ℕ) : IsSequence a → ∀ n, 3 ∣ a n ∧ c_k 3 (a n) = 3 := by
  aesop;
  · contrapose! a_1;
    exact fun h => absurd ( lem_no_v3_zero_terms a h n ) ( by aesop );
  · -- Since $a_n$ is divisible by 3 and even, its smallest divisors are 1, 2, and 3. Therefore, the third smallest divisor is 3.
    have h_divisors : (Nat.divisors (a n)).sort (· ≤ ·) = 1 :: 2 :: 3 :: (Nat.divisors (a n) \\ {1, 2, 3}).sort (· ≤ ·) := by
      rw [ ← Finset.sort_insert ];
      · rw [ ← Finset.sort_insert ];
        · rw [ ← Finset.sort_insert ];
          · -- Since $a_n$ is divisible by 3, the set $\\{1, 2, 3\\}$ is a subset of the divisors of $a_n$.
            have h_subset : {1, 2, 3} ⊆ Nat.divisors (a n) := by
              intro x hx
              aesop;
              · simpa [ a_2 ] using a_1.1 n;
              · exact even_iff_two_dvd.mp ( by exact? );
              · simpa [ a_2 ] using a_1.1 n;
              · contrapose! a_1;
                exact fun h => absurd ( lem_no_v3_zero_terms a h n ) ( by aesop );
              · simpa [ a_2 ] using a_1.1 n;
            congr;
            ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx3 : x = 3 <;> aesop;
            · exact Nat.dvd_of_mem_divisors ( h_subset ( by norm_num ) );
            · exact Nat.dvd_of_mem_divisors ( h_subset ( by norm_num ) );
          · aesop;
            exact Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero right_1 );
          · aesop;
        · aesop;
          exact Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero right_1 ) ) ( Ne.symm left_1 );
        · -- Since $2$ is not in $\\{3\\}$ and $2$ is not in $(Nat.divisors (a n) \\ {1, 2, 3})$, it follows that $2$ is not in their union.
          simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton];
      · -- Since $b$ is a divisor of $a_n$ and $b \\notin \\{1, 2, 3\\}$, the smallest possible value for $b$ is $3$.
        intros b hb
        have hb_pos : 1 ≤ b := by
          exact Nat.pos_of_mem_divisors ( Finset.mem_sdiff.mp hb |>.1 );
        contrapose! hb; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
      · aesop;
    unfold c_k;
    aesop

/-
An infinite sequence cannot have a term $a_n$ with $c_4(a_n) \\ge 7$.
-/
lemma lem_c4_ge_7_impossible (a : ℕ → ℕ) : IsSequence a → ∀ n, ¬ (c_k 4 (a n) ≥ 7) := by
  bound;
  -- Since $a_n$ is divisible by 3, its divisors must include 1, 2, 3, and 6. Therefore, $c_4(a_n)$ cannot be greater than or equal to 7.
  have h_divisors : 3 ∣ a n ∧ c_k 3 (a n) = 3 := by
    exact?;
  have h_ratio : R (a n) < 1 := by
    -- Substitute c_k 3 (a n) = 3 into the expression for R(a n).
    have h_ratio_expr : R (a n) = (1 : ℚ) / 2 + 1 / 3 + 1 / (c_k 4 (a n)) := by
      rw [ lem_ratio_for_even ];
      · rw [ h_divisors.2 ] ; ring;
      · exact?;
      · exact a_1.2.1 n;
    rw [ h_ratio_expr, div_add_div, div_add_div, div_lt_iff₀ ] <;> norm_cast <;> nlinarith;
  unfold R at h_ratio;
  rw [ div_lt_iff₀ ] at h_ratio <;> norm_cast at *;
  · unfold c_k at *;
    rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ ) <;> aesop;
    have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
    interval_cases y <;> interval_cases x <;> simp_all ( config := { decide := Bool.true } );
    all_goals have := k ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 6; simp_all ( config := { decide := Bool.true } ) ;
      contrapose! k;
      exact Or.inl ⟨ ⟨ Nat.lcm_dvd left ( show 2 ∣ a n from even_iff_two_dvd.mp ( by simpa using lem_all_terms_even a a_1 n ) ), by aesop_cat ⟩, by linarith, fun h => by have := left_7 _ h; linarith ⟩;
  · exact a_1.1 n

/-
For any term $a_n$ in a non-constant infinite sequence, if $a_n$ is not a fixed point, then $R(a_n)>1$.
-/
lemma lem_non_fixed_must_grow (a : ℕ → ℕ) : IsSequence a → ∀ n, S (a n) ≠ a n → R (a n) > 1 := by
  -- By Lemma~\\ref{lem:all_terms_divisible_by_3}, we have $c_3(a_n)=3$. By Lemma~\\ref{lem:c4_ge_7_impossible}, we must have $c_4(a_n) < 7$.
  intros ha n hn
  have h_c3 : c_k 3 (a n) = 3 := by
    -- By Lemma~\\ref{lem:all_terms_divisible_by_3}, we have $3 \\mid a_n$ and $c_3(a_n) = 3$.
    apply (lem_all_terms_divisible_by_3 a ha n).right
  have h_c4 : c_k 4 (a n) < 7 := by
    by_contra h_contra;
    have := lem_c4_ge_7_impossible a ha n;
    exact this ( not_lt.mp h_contra );
  -- Since $c_4(a_n)$ must be 4 or 5, we can calculate $R(a_n)$ for these cases.
  have h_cases : c_k 4 (a n) = 4 ∨ c_k 4 (a n) = 5 := by
    interval_cases _ : c_k 4 ( a n ) <;> simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
      · replace x := congr_arg List.length x ; simp_all ( config := { decide := Bool.true } );
        have := ha.2.1 n; rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
    · unfold c_k at *;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
      have := x ▸ Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( a n |> Nat.divisors ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
      · have := x ▸ Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
      · have := x ▸ Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      -- Since the divisors are sorted in ascending order, having two consecutive divisors both equal to 3 isn't possible. This means our assumption must be wrong, leading to a contradiction.
      have h_unique_divisors : List.Nodup (Finset.sort (· ≤ ·) (Nat.divisors (a n))) := by
        exact Finset.sort_nodup _ _;
      rcases x : Finset.sort ( · ≤ · ) ( Nat.divisors ( a n ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · -- If $c_4(a_n) = 6$, then $R(a_n) = \\frac{1}{2} + \\frac{1}{3} + \\frac{1}{6} = 1$, so $a_n$ is a fixed point by Lemma~\\ref{lem:fixed_point_condition}.
      have h_fixed_point : R (a n) = 1 := by
        rw [ lem_ratio_for_even ];
        · norm_num [ h_c3, ‹c_k 4 ( a n ) = 6› ];
        · exact?;
        · exact ha.2.1 n;
      have := lem_fixed_point_condition ( a n ) ( ha.1 n ) ; aesop;
  have h_ratio : R (a n) = (1 : ℚ) / 2 + 1 / (c_k 3 (a n)) + 1 / (c_k 4 (a n)) := by
    apply lem_ratio_for_even;
    · exact?;
    · exact ha.2.1 n;
  rcases h_cases with ( h | h ) <;> norm_num [ h_ratio, h_c3, h ]

/-
Any possible value of $a_1$ must be of the form $6 \\cdot 12^a \\cdot m$ for some integer $a \\ge 0$ and a positive integer $m$ with $\\gcd(m,10)=1$.
-/
lemma lem_a1_structure :
  { a₁ | ∃ a : ℕ → ℕ, IsSequence a ∧ a₁ = a 0 } ⊆ { n | ∃ a m, m > 0 ∧ Nat.Coprime m 10 ∧ n = 6 * 12 ^ a * m } := by
    -- Therefore, any term $a_n$ in the sequence must be of the form $6 \\cdot 12^k \\cdot m$ where $m$ is coprime to 10.
    intros a₁ ha₁
    obtain ⟨a, ha_seq, rfl⟩ := ha₁;
    -- Let $k$ be such that $a_k$ is the first fixed point in the sequence.
    obtain ⟨k, hk⟩ : ∃ k, S (a k) = a k ∧ ∀ j < k, S (a j) ≠ a j := by
      -- By the well-ordering principle, there exists a smallest $k$ such that $S(a_k) = a_k$.
      obtain ⟨k, hk⟩ : ∃ k, S (a k) = a k := by
        -- By contradiction, assume there is no such $k$.
        by_contra h_no_fixed_point;
        -- Since $a_n$ is not a fixed point, we have $R(a_n) > 1$ for all $n$.
        have hR_gt_1 : ∀ n, R (a n) > 1 := by
          intros n;
          apply_rules [ lem_non_fixed_must_grow ];
          exact fun h => h_no_fixed_point ⟨ n, h ⟩;
        -- Since $R(a_n) > 1$, we have $a_{n+1} = a_n \\cdot R(a_n) > a_n$ for all $n$.
        have h_increasing : ∀ n, a (n + 1) > a n := by
          unfold R at hR_gt_1;
          intro n; specialize hR_gt_1 n; rw [ gt_iff_lt, lt_div_iff₀ ] at hR_gt_1 <;> norm_cast at * <;> aesop;
          · exact ha_seq.2.2 n ▸ hR_gt_1;
          · exact ha_seq.1 n;
        -- Since $a_n$ is strictly increasing, it cannot have a term $a_k$ with $c_4(a_k) \\ge 7$.
        have h_c4_lt_7 : ∀ n, c_k 4 (a n) < 7 := by
          intros n
          by_contra h_contra;
          exact absurd ( lem_c4_ge_7_impossible a ha_seq n ) ( by aesop );
        -- Since $c_4(a_n) < 7$, we have $c_4(a_n) = 4$ or $c_4(a_n) = 5$ for all $n$.
        have h_c4_eq_4_or_5 : ∀ n, c_k 4 (a n) = 4 ∨ c_k 4 (a n) = 5 := by
          intros n
          have h_c4_divisors : c_k 2 (a n) = 2 ∧ c_k 3 (a n) = 3 := by
            have := lem_all_terms_divisible_by_3 a ha_seq n;
            have := lem_c2_is_2 a ha_seq n; aesop;
          have h_c4_gt_c3 : c_k 4 (a n) > c_k 3 (a n) := by
            unfold c_k at *;
            rcases x : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( a n |> Nat.divisors ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> aesop;
            · have := ha_seq.2.1 n; replace x := congr_arg List.length x; aesop;
              rw [ ← Nat.cons_self_properDivisors ] at x <;> aesop;
            · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              rcases k with ( _ | _ | _ | _ | k ) <;> simp_all +arith +decide;
              have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
          have := h_c4_lt_7 n; interval_cases _ : c_k 4 ( a n ) <;> simp_all ( config := { decide := Bool.true } ) ;
          have := lem_ratio_for_even ( a n ) ( by
            exact? ) ( by
            exact ha_seq.2.1 n ) ; simp_all ( config := { decide := Bool.true } );
          linarith [ hR_gt_1 n ];
        -- Since $c_4(a_n) = 4$ or $c_4(a_n) = 5$, we have $R(a_n) = \\frac{13}{12}$ or $R(a_n) = \\frac{31}{30}$ for all $n$.
        have hR_eq_13_12_or_31_30 : ∀ n, R (a n) = 13 / 12 ∨ R (a n) = 31 / 30 := by
          intros n
          obtain h | h := h_c4_eq_4_or_5 n;
          · have hR_eq_13_12 : R (a n) = 1 / 2 + 1 / 3 + 1 / 4 := by
              rw [ lem_ratio_for_even ];
              · have := lem_all_terms_divisible_by_3 a ha_seq n; aesop;
              · exact?;
              · exact ha_seq.2.1 n;
            exact Or.inl <| hR_eq_13_12.trans <| by norm_num;
          · have hR_eq_31_30 : R (a n) = (1 : ℚ) / 2 + 1 / (c_k 3 (a n)) + 1 / (c_k 4 (a n)) := by
              rw [ lem_ratio_for_even ];
              · exact?;
              · exact ha_seq.2.1 n;
            have h_c3_eq_3 : c_k 3 (a n) = 3 := by
              have := lem_all_terms_divisible_by_3 a ha_seq n;
              exact this.2;
            norm_num [ hR_eq_31_30, h_c3_eq_3, h ];
        -- Since $R(a_n) = \\frac{13}{12}$ or $R(a_n) = \\frac{31}{30}$, we have $a_{n+1} = a_n \\cdot \\frac{13}{12}$ or $a_{n+1} = a_n \\cdot \\frac{31}{30}$ for all $n$.
        have h_an1_eq_an_mul_13_12_or_31_30 : ∀ n, a (n + 1) = a n * (13 / 12 : ℚ) ∨ a (n + 1) = a n * (31 / 30 : ℚ) := by
          intro n; specialize hR_eq_13_12_or_31_30 n; unfold R at hR_eq_13_12_or_31_30; aesop;
          · exact Or.inl ( by rw [ ← h, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr ( by linarith [ ha_seq.1 n ] ) ) ] ; rw [ ha_seq.2.2 ] );
          · rw [ div_eq_iff ] at h_1 <;> norm_num [ ha_seq.2.2 ] at *;
            · exact Or.inr ( by linarith );
            · linarith [ ha_seq.1 n ];
        -- Since $a_{n+1} = a_n \\cdot \\frac{13}{12}$ or $a_{n+1} = a_n \\cdot \\frac{31}{30}$, we have $a_n = a_0 \\cdot \\left(\\frac{13}{12}\\right)^{k} \\cdot \\left(\\frac{31}{30}\\right)^{m}$ for some $k, m \\geq 0$.
        have h_an_form : ∀ n, ∃ k m : ℕ, a n = a 0 * (13 / 12 : ℚ) ^ k * (31 / 30 : ℚ) ^ m := by
          intro n;
          induction' n with n ih;
          · exact ⟨ 0, 0, by norm_num ⟩;
          · rcases ih with ⟨ k, m, ih ⟩ ; rcases h_an1_eq_an_mul_13_12_or_31_30 n with h | h <;> [ exact ⟨ k + 1, m, by rw [ h, ih ] ; ring ⟩ ; exact ⟨ k, m + 1, by rw [ h, ih ] ; ring ⟩ ];
        choose k m hkm using h_an_form;
        -- Since $a_n$ is an integer, the denominator $12^{k_n} \\cdot 30^{m_n}$ must divide $a_0$.
        have h_denom_divides_a0 : ∀ n, 12 ^ k n * 30 ^ m n ∣ a 0 := by
          -- Since $a_n$ is an integer, the denominator $12^{k_n} \\cdot 30^{m_n}$ must divide the numerator $a_0 \\cdot 13^{k_n} \\cdot 31^{m_n}$.
          have h_denom_divides_num : ∀ n, 12 ^ k n * 30 ^ m n ∣ a 0 * 13 ^ k n * 31 ^ m n := by
            intro n; specialize hkm n; rw [ div_pow, div_pow ] at hkm;
            field_simp at hkm;
            norm_cast at hkm; exact hkm ▸ dvd_mul_left _ _;
          intro n; specialize h_denom_divides_num n;
          refine' Nat.Coprime.dvd_of_dvd_mul_right _ _;
          exact 13 ^ k n * 31 ^ m n;
          · apply_rules [ Nat.Coprime.mul, Nat.Coprime.pow ];
            · apply_rules [ Nat.Coprime.mul_right, Nat.Coprime.pow ];
            · apply_rules [ Nat.Coprime.mul_right, Nat.Coprime.pow ];
          · simpa only [ mul_assoc ] using h_denom_divides_num;
        -- Since $12^{k_n} \\cdot 30^{m_n}$ divides $a_0$, and $a_0$ is fixed, the sequence $12^{k_n} \\cdot 30^{m_n}$ must be bounded.
        have h_denom_bounded : ∃ M, ∀ n, 12 ^ k n * 30 ^ m n ≤ M := by
          exact ⟨ a 0, fun n => Nat.le_of_dvd ( ha_seq.1 0 ) ( h_denom_divides_a0 n ) ⟩;
        -- Since $12^{k_n} \\cdot 30^{m_n}$ is bounded, the sequence $k_n + m_n$ must also be bounded.
        have h_k_m_bounded : ∃ M, ∀ n, k n + m n ≤ M := by
          obtain ⟨ M, hM ⟩ := h_denom_bounded;
          use M;
          intro n; specialize hM n; contrapose! hM;
          refine' lt_of_lt_of_le hM _;
          -- Since $12^{k_n} \\cdot 30^{m_n}$ grows exponentially, we have $k_n + m_n \\leq 12^{k_n} \\cdot 30^{m_n}$.
          have h_exp_growth : ∀ k m : ℕ, k + m ≤ 12 ^ k * 30 ^ m := by
            intro k m; induction' k with k ih generalizing m <;> induction' m with m ih' <;> norm_num [ Nat.pow_succ', mul_assoc ] at *;
            · linarith [ pow_pos ( by decide : 0 < 30 ) m ];
            · linarith [ ih 0, Nat.one_le_pow k 12 ( by decide ) ];
            · linarith [ ih m ];
          exact h_exp_growth _ _;
        -- Since $k_n + m_n$ is bounded, the sequence $a_n$ must also be bounded.
        have h_an_bounded : ∃ M, ∀ n, a n ≤ M := by
          use a 0 * 13 ^ h_k_m_bounded.choose * 31 ^ h_k_m_bounded.choose;
          intro n;
          have := hkm n;
          rw [ ← @Nat.cast_le ℚ ];
          rw [ this ] ; push_cast ; ring_nf;
          gcongr;
          · exact le_trans ( pow_le_pow_left ( by norm_num ) ( by norm_num ) _ ) ( pow_le_pow_right₀ ( by norm_num ) ( show m n ≤ h_k_m_bounded.choose from by linarith [ h_k_m_bounded.choose_spec n ] ) );
          · exact le_trans ( pow_le_pow_left ( by norm_num ) ( by norm_num ) _ ) ( pow_le_pow_right₀ ( by norm_num ) ( h_k_m_bounded.choose_spec n |> le_trans ( Nat.le_add_right _ _ ) ) );
        exact absurd ( Set.infinite_range_of_injective ( StrictMono.injective ( strictMono_nat_of_lt_succ h_increasing ) ) ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ h_an_bounded.choose, Set.forall_mem_range.mpr fun n => h_an_bounded.choose_spec n ⟩ );
      exact ⟨ Nat.find ( ⟨ k, hk ⟩ : ∃ k, S ( a k ) = a k ), Nat.find_spec ( ⟨ k, hk ⟩ : ∃ k, S ( a k ) = a k ), fun j hj => Nat.find_min ( ⟨ k, hk ⟩ : ∃ k, S ( a k ) = a k ) hj ⟩;
    -- By Lemma~\\ref{lem:transition_to_v3_positive_is_odd}, the term $a_{k-1}$ must have $v_2(a_{k-1}) \\ge 2$.
    have h_ak_minus_1 : ∀ j < k, a (j + 1) = a j * (13 / 12 : ℚ) := by
      -- Since $a_j$ is not a fixed point, we have $R(a_j) > 1$ and $c_3(a_j) = 3$, $c_4(a_j) = 4$.
      have h_R_gt_1_and_c3_c4 : ∀ j < k, R (a j) > 1 ∧ c_k 3 (a j) = 3 ∧ c_k 4 (a j) = 4 := by
        intros j hj;
        -- Since $a_j$ is not a fixed point, by Lemma~\\ref{lem:all_terms_divisible_by_3}, $a_j$ is divisible by 3, so $c_k 3 (a_j) = 3$.
        have h_c3 : c_k 3 (a j) = 3 := by
          exact lem_all_terms_divisible_by_3 a ha_seq j |>.2;
        have h_R_gt_1 : R (a j) > 1 := by
          exact lem_non_fixed_must_grow a ha_seq j ( hk.2 j hj );
        have := lem_growth_condition ( a j ) ?_ ?_ ?_ <;> aesop;
        · have := lem_growth_c4_is_5_impossible ( a j ) ?_ ?_ ?_ ?_;
          · -- Since $a_j$ is even, $S(a_j)$ must also be even. This contradicts the fact that $S(a_j)$ is odd.
            have h_even_S : Even (S (a j)) := by
              have h_even_S : Even (a (j + 1)) := by
                exact?;
              exact ha_seq.2.2 j ▸ h_even_S;
            exact Nat.not_even_iff_odd.mpr this h_even_S;
          · -- Since $a$ is a sequence, we have $a (n + 1) = S (a n)$ for all $n$.
            have h_seq : ∀ n, a (n + 1) = S (a n) := by
              exact fun n => ha_seq.2.2 n;
            constructor <;> aesop;
            · exact ha_seq.1 j;
            · have := ha_seq.1 ( j + n );
              convert this using 1;
              exact Nat.recOn n ( by norm_num ) fun n ih => by rw [ Nat.add_succ, h_seq, Function.iterate_succ_apply', ih ] ;
            · exact ha_seq.2.1 j;
            · -- Since $a$ is a sequence, each term $a n$ has at least three proper divisors. Therefore, $S^[n] (a j)$ is just another term in the sequence, and thus has at least three proper divisors.
              have h_seq_divisors : ∀ n, 3 ≤ (Nat.properDivisors (a n)).card := by
                exact fun n => ha_seq.2.1 n;
              convert h_seq_divisors ( j + n ) using 1;
              exact congr_arg ( fun x => ( Nat.properDivisors x ).card ) ( Nat.recOn n ( by norm_num ) fun n ih => by rw [ Nat.add_succ, h_seq, Function.iterate_succ_apply', ih ] );
            · exact Nat.recOn n ( by norm_num ) fun n ih => by rw [ Function.iterate_succ_apply', ih, Function.iterate_succ_apply' ] ;
          · exact lem_c2_is_2 a ha_seq j;
          · exact h_c3;
          · exact h_1;
        · exact?;
      intro j hj;
      have := h_R_gt_1_and_c3_c4 j hj;
      have h_S_a_j : S (a j) = a j * (13 / 12 : ℚ) := by
        unfold R at this;
        have := lem_ratio_for_even ( a j ) ( by
          exact? ) ( by
          exact ha_seq.2.1 j ) ; aesop;
        rw [ lt_div_iff₀ ] at this_1 <;> norm_num at *;
        · unfold R at this;
          rw [ ← this, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr <| by specialize ha_seq; have := ha_seq.1 j; aesop ) ];
        · exact Nat.pos_of_ne_zero ( by specialize ha_seq; have := ha_seq.1 j; aesop );
      rw [ ← h_S_a_j, ha_seq.2.2 ];
    -- Therefore, $a_0 = a_k \\cdot \\left(\\frac{12}{13}\\right)^k$.
    have h_a0 : a 0 = a k * (12 / 13 : ℚ) ^ k := by
      have h_a0 : ∀ j ≤ k, a j = a 0 * (13 / 12 : ℚ) ^ j := by
        intro j hj;
        induction' j with j ih;
        · norm_num;
        · rw [ h_ak_minus_1 j ( Nat.lt_of_succ_le hj ), ih ( Nat.le_of_succ_le hj ), pow_succ, mul_assoc ];
      rw [ h_a0 k le_rfl ] ; ring;
      norm_num [ mul_assoc, ← mul_pow ];
    -- Since $a_k$ is a fixed point, by Lemma~\\ref{lem:fixed_point_form}, $a_k$ must be of the form $6m'$ where $m'$ is coprime to 10.
    obtain ⟨m', hm'_pos, hm'_coprime, hm'_eq⟩ : ∃ m', 0 < m' ∧ Nat.Coprime m' 10 ∧ a k = 6 * m' := by
      have := lem_fixed_point_form ( a k );
      exact this.mp ⟨ hk.1, ha_seq.2.1 k ⟩;
    -- Substitute $a_k = 6m'$ into the equation $a_0 = a_k \\cdot \\left(\\frac{12}{13}\\right)^k$ to get $a_0 = 6m' \\cdot \\left(\\frac{12}{13}\\right)^k$.
    rw [hm'_eq] at h_a0;
    -- For $a_0$ to be an integer, $m'$ must be divisible by $13^k$. Let $m' = 13^k \\cdot m$ for some integer $m$.
    obtain ⟨m, hm⟩ : ∃ m, m' = 13^k * m := by
      have h_div : 13^k ∣ 6 * m' := by
        field_simp at h_a0;
        norm_cast at h_a0;
        exact ( Nat.Coprime.dvd_of_dvd_mul_right ( by cases k <;> norm_num ) <| h_a0 ▸ dvd_mul_left _ _ );
      exact ( Nat.Coprime.dvd_of_dvd_mul_left ( by cases k <;> norm_num ) h_div );
    refine' ⟨ k, m, _, _, _ ⟩ <;> simp_all ( config := { decide := Bool.true } ) [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ];
    · exact hm'_coprime.2;
    · rw [ ← @Nat.cast_inj ℚ ] ; push_cast [ h_a0 ] ; ring;
      -- By simplifying, we can see that $(12/13)^k * 13^k = 12^k$.
      field_simp

/-
A proper divisor of a positive integer $N$ is a positive divisor of $N$ other than $N$ itself.
The infinite sequence $a_1,a_2,...$ consists of positive integers, each of which has at least three proper divisors.
For each $n \\ge 1$, the integer $a_{n+1}$ is the sum of the three largest proper divisors of $a_n$.
The set of all possible values of $a_1$ is the set of all integers of the form $6 \\cdot 12^a \\cdot m$, for any integer $a \\ge 0$ and any positive integer $m$ which is coprime to $10$.
-/
theorem main_theorem :
    { a₁ | ∃ a : ℕ → ℕ,
      (∀ n, 0 < a n) ∧
      (∀ n, 3 ≤ (a n).properDivisors.card) ∧
      (∀ n, a (n+1) =
        ((a n).properDivisors.sort (· ≥ ·))[0]! +
        ((a n).properDivisors.sort (· ≥ ·))[1]! +
        ((a n).properDivisors.sort (· ≥ ·))[2]!) ∧
      a₁ = a 0
    } = { n | ∃ a m, m > 0 ∧ m.Coprime 10 ∧ n = 6 * 12 ^ a * m } := by
      ext a₁;
      constructor;
      · intro ha₁;
        -- By lemma lem_a1_structure, any possible value of $a_1$ must be of the form $6 \\cdot 12^a \\cdot m$ for some integer $a \\ge 0$ and a positive integer $m$ with $\\gcd(m,10)=1$.
        apply lem_a1_structure;
        obtain ⟨a, ha⟩ := ha₁;
        exact ⟨ a, ⟨ ha.1, ha.2.1, ha.2.2.1 ⟩, ha.2.2.2 ⟩;
      · -- By definition of $a₁$, we know that there exist $a$ and $m$ such that $a₁ = 6 * 12^a * m$ and $m$ is coprime to 10.
        intro h
        obtain ⟨a, m, hm_pos, hm_coprime, rfl⟩ := h;
        -- Apply the lemma lem_verification_of_form to obtain the required sequence a and show that a 0 equals 6 * 12^a * m.
        obtain ⟨a, ha⟩ := lem_verification_of_form ⟨a, m, hm_pos, hm_coprime, rfl⟩;
        exact ⟨ a, ha.1.1, ha.1.2.1, ha.1.2.2, ha.2 ⟩

#print axioms main_theorem
`,T=`/-
Alice and Bazza are playing the \\emph{inekoalaty game}, a two-player game whose rules depend on a positive real number $\\lambda$ which is known to both players. On the $n^\\text{th}$ turn of the game (starting with $n=1$) the following happens:
\\begin{itemize}
        \\item If $n$ is odd, Alice chooses a nonnegative real number $x_n$ such that
        \\[ x_1 + x_2 + \\dots + x_n \\leqslant \\lambda n.\\]
        \\item If $n$ is even, Bazza chooses a nonnegative real number $x_n$ such that
        \\[ x_1^2 + x_2^2 + \\dots + x_n^2 \\leqslant n.\\]
\\end{itemize}
If a player cannot choose a suitable number $x_n$, the game ends and the other player wins. If the game goes on forever, neither player wins. All chosen numbers are known to both players.

Determine all values of $\\lambda$ for which Alice has a winning strategy and all those for which Bazza has a winning strategy.

Answer: Alice wins if $\\lambda > 1 / \\sqrt{2}$. Bazza wins if $0 < \\lambda < 1 / \\sqrt{2}$.
-/

import HarmonicLean.Imports

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace IMO2025P5

/- Alice's strategy: given a tuple of nonnegative reals of even length,
yields the next number. -/
abbrev AliceStrategy : Type := ∀ n, (Fin (2 * n) → NNReal) → NNReal
/- Bazza's strategy: given a tuple of nonnegative reals of odd length,
yields the next number. -/
abbrev BazzaStrategy : Type := ∀ n, (Fin (2 * n + 1) → NNReal) → NNReal

/- The sequence of numbers produced by a couple of strategies. -/
def play (alice : AliceStrategy) (bazza : BazzaStrategy) : ℕ → NNReal
  | n =>
    if n % 2 = 0 then alice (n / 2) fun k ↦ play alice bazza k
    else bazza (n / 2) fun k ↦ play alice bazza k

/-
The predicate saying that \`n\` move in the sequence \`xs 0, xs 1, ...\` is valid.
For even values of \`n\`, it checks that \`∑ k ≤ n, xs k ≤ lam * (n + 1)\`.
For odd values of \`n\`, it checks that \`∑ k ≤ n, (xs k) ^ 2 ≤ n + 1\`.
-/
def ValidMove (lam : ℝ) (xs : ℕ → NNReal) (n : ℕ) : Prop :=
  if Even n then ∑ k ≤ n, xs k ≤ lam * (n + 1)
  else ∑ k ≤ n, (xs k) ^ 2 ≤ n + 1

/-- The predicate saying that a given Alice's strategy is a winning one. -/
def AliceStrategy.Wins (lam : ℝ) (alice : AliceStrategy) : Prop :=
  ∀ bazza, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazza) m} n ∧ Odd n

/-- The predicate saying that a given Bazza's strategy is a winning one. -/
def BazzaStrategy.Wins (lam : ℝ) (bazza : BazzaStrategy) : Prop :=
  ∀ alice, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazza) m} n ∧ Even n

/-
For a sequence of moves $x_1, x_2, \\dots$ in the inekoalaty game, we define the partial sum of values $S_n = \\sum_{i=1}^n x_i$ and the partial sum of squares $Q_n = \\sum_{i=1}^n x_i^2$. We adopt the convention that $S_0=0$ and $Q_0=0$.
-/
def s (xs : ℕ → NNReal) (n : ℕ) : ℝ := ∑ i in Finset.range n, (xs i : ℝ)
def q (xs : ℕ → NNReal) (n : ℕ) : ℝ := ∑ i in Finset.range n, (xs i : ℝ) ^ 2

/-
Bazza's reference strategy is as follows: on his turn $2k$, if he has not already lost (i.e., if $Q_{2k-1} \\le 2k$), he chooses $x_{2k} = \\sqrt{2k - Q_{2k-1}}$.
-/
def bazzaReferenceStrategy : BazzaStrategy := fun n hist ↦
  let Q_2n_plus_1 := ∑ i, (hist i : ℝ) ^ 2
  let val_sq := (2 * (n + 1) : ℝ) - Q_2n_plus_1
  if h : 0 ≤ val_sq then
    NNReal.sqrt ⟨val_sq, h⟩
  else
    0

/-
Let $f(k) = \\frac{k\\sqrt{2}}{2k-1}$ for $k \\ge 1$.
-/
def f (k : ℕ) : ℝ := (k : ℝ) * Real.sqrt 2 / (2 * (k : ℝ) - 1)

/-
For a given $\\lambda > 1/\\sqrt{2}$, Alice's reference strategy is as follows: first, choose an integer $K$ according to Lemma~\\ref{lem:existence_of_K_for_alice} such that $\\lambda > \\frac{K\\sqrt{2}}{2K-1}$.
Then, for all turns $2k-1$ with $k < K$, Alice chooses $x_{2k-1}=0$. At turn $2K-1$, Alice chooses $x_{2K-1} = \\lambda(2K-1) - S_{2K-2}$.
-/
def aliceReferenceStrategy (lam : ℝ) (K : ℕ) : AliceStrategy := fun n hist ↦
  if n + 1 < K then
    0
  else if n + 1 = K then
    let S_2n := ∑ i, (hist i : ℝ)
    let move := lam * (2 * (n + 1) - 1) - S_2n
    if h_nonneg : 0 ≤ move then
      ⟨move, h_nonneg⟩
    else
      0
  else
    0

/-
If Bazza uses his reference strategy (Definition~\\ref{def:bazza_strategy}) and can make a move at turn $2k$, then $Q_{2k}=2k$.
-/
lemma lemBazzaStrategyQValue (n : ℕ) (h : Fin (2 * n + 1) → NNReal)
  (h_can_move : (∑ i, (h i : ℝ) ^ 2) ≤ (2 * (n + 1) : ℝ)) :
  let x_2np1 := bazzaReferenceStrategy n h
  (∑ i, (h i : ℝ) ^ 2) + (x_2np1 : ℝ) ^ 2 = (2 * (n + 1) : ℝ) := by
  unfold bazzaReferenceStrategy;
  aesop

/-
If Bazza uses his reference strategy and neither player has won by turn $2k-1$, then $Q_{2k-2} = 2(k-1)$ for $k \\ge 2$. For $k=1$, $Q_0=0$ by Definition~\\ref{def:sums}.
-/
lemma lemQ_2k_minus_2_under_bazza_ref (lam : ℝ) (alice : AliceStrategy) (k : ℕ) (hk : 1 ≤ k)
  (h_not_won : ∀ m < 2 * k - 2, ValidMove lam (play alice bazzaReferenceStrategy) m) :
  q (play alice bazzaReferenceStrategy) (2 * (k - 1)) = (2 * (k - 1) : ℝ) := by
  -- For the case when $k = 1$, we have $2 * (k - 1) = 0$, and the sum of squares up to 0 is 0, which matches $2 * (1 - 1) = 0$.
  by_cases hk1 : k = 1;
  · aesop;
  · rcases k with ( _ | _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    have h_q_2k : (∑ i in Finset.range (2 * k + 1), (play alice bazzaReferenceStrategy i : ℝ) ^ 2) ≤ (2 * (k + 1) : ℝ) := by
      specialize h_not_won ( 2 * k + 1 ) ; unfold ValidMove at h_not_won ; aesop;
      norm_cast;
      refine le_trans ?_ ( h_not_won.trans ?_ );
      · exact Finset.sum_le_sum_of_subset ( fun x hx => Finset.mem_Iic.mpr ( Finset.mem_range_le hx |> le_trans <| Nat.le_refl _ ) );
      · norm_cast;
    -- By definition of $q$, we can write
    have h_q_def : q (play alice bazzaReferenceStrategy) (2 * k + 2) = (∑ i in Finset.range (2 * k + 1), (play alice bazzaReferenceStrategy i : ℝ) ^ 2) + (bazzaReferenceStrategy k (fun i => play alice bazzaReferenceStrategy i) : ℝ) ^ 2 := by
      unfold q;
      rw [Finset.sum_range_succ];
      unfold play;
      norm_num +zetaDelta at *;
      rw [ show ( 2 * k + 1 ) / 2 = k by omega ];
      congr! 2;
      exact?;
    convert lemBazzaStrategyQValue k _ _ using 1;
    convert h_q_def;
    · rw [ Finset.sum_range ];
    · simpa only [ Finset.sum_range ] using h_q_2k

/-
If Alice does not win at turn $2j-1$ against Bazza's reference strategy, then the sum of that turn's moves is $x_{2j-1}+x_{2j} \\ge \\sqrt{2}$.
-/
lemma lemPairSumLowerBound (xs : ℕ → NNReal) (j : ℕ) (hj : 1 ≤ j)
  (h_q_prev : q xs (2 * (j - 1)) = (2 * (j - 1) : ℝ))
  (h_bazza_move : xs (2 * j - 1) = bazzaReferenceStrategy (j - 1) fun i ↦ xs i.val)
  (h_not_win : ¬ (q xs (2 * j - 1) > (2 * j : ℝ))) :
  (xs (2 * j - 2) : ℝ) + (xs (2 * j - 1) : ℝ) ≥ Real.sqrt 2 := by
  -- By definition of $bazzaReferenceStrategy$, we know that $x_{2j} = \\sqrt{2 - x_{2j-1}^2}$.
  have h_bazza_move_value : (xs (2 * j - 1) : ℝ) = Real.sqrt (2 - (xs (2 * j - 2) : ℝ) ^ 2) := by
    rcases j with ⟨ _ | j ⟩ <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, Finset.sum_range_succ ];
    unfold bazzaReferenceStrategy;
    simp_all ( config := { decide := Bool.true } ) [ Fin.sum_univ_castSucc, q ];
    split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ Finset.sum_range ];
    · ring;
    · rw [ Real.sqrt_eq_zero_of_nonpos ] ; linarith;
  by_cases h_case : (xs (2 * j - 2) : ℝ) ≤ Real.sqrt 2;
  · field_simp;
    rw [ h_bazza_move_value, Real.sqrt_le_left ];
    · nlinarith only [ Real.sqrt_nonneg ( 2 - ( xs ( 2 * j - 2 ) : ℝ ) ^ 2 ), Real.mul_self_sqrt ( show 0 ≤ 2 - ( xs ( 2 * j - 2 ) : ℝ ) ^ 2 by nlinarith only [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), h_case, show ( xs ( 2 * j - 2 ) : ℝ ) ≥ 0 by positivity ] ), show ( xs ( 2 * j - 2 ) : ℝ ) ≥ 0 by positivity ];
    · positivity;
  · exact le_add_of_le_of_nonneg ( le_of_not_le h_case ) ( NNReal.coe_nonneg _ )

/-
If Bazza uses his reference strategy and Alice has not won by turn $2k-1$, then $S_{2k-2} \\ge (k-1)\\sqrt{2}$ for $k \\ge 1$.
-/
lemma lemSLowerBound (lam : ℝ) (alice : AliceStrategy) (k : ℕ) (hk : 1 ≤ k)
  (h_not_won : ∀ m < 2 * k - 2, ValidMove lam (play alice bazzaReferenceStrategy) m) :
  s (play alice bazzaReferenceStrategy) (2 * (k - 1)) ≥ ((k - 1) : ℝ) * Real.sqrt 2 := by
  -- By Lemma~\\ref{lem:pair_sum_lower_bound}, for each $j$ from $1$ to $k-1$, we have $x_{2j-1} + x_{2j} \\ge \\sqrt{2}$.
  have h_pair_sum_lower_bound : ∀ j ∈ Finset.Ico 1 k, (play alice bazzaReferenceStrategy (2 * j - 2) : ℝ) + (play alice bazzaReferenceStrategy (2 * j - 1) : ℝ) ≥ Real.sqrt 2 := by
    intro j hj;
    apply_rules [ lemPairSumLowerBound ];
    · -- Since $j$ is in the Finset.Ico 1 k, we have $1 \\leq j$.
      aesop;
    · -- Apply the lemma that states if Bazza uses his reference strategy and neither player has won by turn $2k-1$, then $Q_{2k-2} = 2(k-1)$.
      apply lemQ_2k_minus_2_under_bazza_ref;
      exacts [ Finset.mem_Ico.mp hj |>.1, fun m hm => h_not_won m ( by linarith [ Finset.mem_Ico.mp hj |>.2, Nat.sub_add_cancel ( by linarith [ Finset.mem_Ico.mp hj |>.1, Finset.mem_Ico.mp hj |>.2 ] : 2 ≤ 2 * k ), Nat.sub_add_cancel ( by linarith [ Finset.mem_Ico.mp hj |>.1, Finset.mem_Ico.mp hj |>.2 ] : 2 ≤ 2 * j ) ] ) ];
    · unfold play;
      -- Since $2j-1$ is odd, $(2j-1) \\% 2 = 1$, so the if condition is false.
      have h_odd : (2 * j - 1) % 2 = 1 := by
        cases j <;> norm_num [ Nat.add_mod, Nat.mul_succ ] at *;
      rw [ if_neg ];
      · rw [ show ( 2 * j - 1 ) / 2 = j - 1 by omega ];
        congr!;
        exact?;
      · -- Since $h_odd$ states that $(2 * j - 1) \\% 2 = 1$, we can directly conclude that $(2 * j - 1) \\% 2 \\neq 0$.
        aesop;
    · rcases j with ( _ | j ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
      have := h_not_won ( 2 * j + 1 ) ( by omega );
      unfold ValidMove at this; aesop;
      exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun i hi => Finset.mem_Iic.mpr ( by linarith [ Finset.mem_range.mp hi ] ) ) fun _ _ _ => sq_nonneg _ ) ( mod_cast this );
  -- By summing the inequalities from h_pair_sum_lower_bound over all j from 1 to k-1, we get the desired result.
  have h_sum_pairs : ∑ j in Finset.Ico 1 k, ((play alice bazzaReferenceStrategy (2 * j - 2) : ℝ) + (play alice bazzaReferenceStrategy (2 * j - 1) : ℝ)) ≥ (k - 1) * Real.sqrt 2 := by
    exact le_trans ( by norm_num [ hk ] ) ( Finset.sum_le_sum h_pair_sum_lower_bound );
  convert h_sum_pairs using 1;
  unfold s;
  exact Nat.recOn k ( by norm_num ) fun n ih => by cases n <;> norm_num [ Nat.mul_succ, Finset.sum_range_succ, Finset.sum_Ico_succ_top ] at * ; linarith;

/-
The limit of $f(k)$ from Definition~\\ref{def:f_function} as $k \\to \\infty$ is $1/\\sqrt{2}$.
-/
lemma lemFLimit : Filter.Tendsto f Filter.atTop (nhds (1 / Real.sqrt 2)) := by
  unfold f;
  -- We can divide the numerator and the denominator by $k$ and then take the limit as $k$ approaches infinity.
  have h_div : Filter.Tendsto (fun k : ℕ => (Real.sqrt 2) / (2 - 1 / (k : ℝ))) Filter.atTop (nhds (Real.sqrt 2 / 2)) := by
    exact le_trans ( tendsto_const_nhds.div ( tendsto_const_nhds.sub <| tendsto_one_div_atTop_nhds_zero_nat ) <| by norm_num ) <| by norm_num;
  refine Filter.Tendsto.congr' ?_ ( h_div.trans ?_ );
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using by simpa [ -one_div, field_simps, hk.ne' ] using by ring;
  · norm_num [ Real.sqrt_div_self ]

/-
If $0 < \\lambda < 1/\\sqrt{2}$, Bazza has a winning strategy.
-/
lemma lemBazzaWinsSmallLambda (lam : ℝ) (hlam : 0 < lam ∧ lam < 1 / Real.sqrt 2) :
  ∃ bazza, BazzaStrategy.Wins lam bazza := by
  -- By Lemma~\\ref{lem:alice_cannot_win_small_lambda}, if $\\lambda \\le 1/\\sqrt{2}$, Alice cannot have a winning strategy. Therefore, Bazza's reference strategy must be a winning strategy.
  have h_bazza_wins : ∀ alice : AliceStrategy, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazzaReferenceStrategy) m} n ∧ Even n := by
    bound;
    by_contra h_contra;
    -- If Alice cannot win, then for all $n$, the game continues.
    have h_game_continues : ∀ n, ValidMove lam (play alice bazzaReferenceStrategy) n := by
      intro n;
      induction' n using Nat.strong_induction_on with n ih;
      rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
      · unfold ValidMove;
        contrapose! h_contra;
        use 2 * k;
        unfold ValidMove;
        unfold IsLeast;
        aesop;
        intro m hm;
        contrapose! hm;
        unfold ValidMove at ih; aesop;
      · have h_q_prev : q (play alice bazzaReferenceStrategy) (2 * k) = (2 * k : ℝ) := by
          convert lemQ_2k_minus_2_under_bazza_ref lam alice ( k + 1 ) ( by linarith ) _ using 1;
          · norm_num;
          · grind;
        unfold ValidMove;
        have h_not_win : ¬ (q (play alice bazzaReferenceStrategy) (2 * k + 1) > (2 * (k + 1) : ℝ)) := by
          have h_not_win : (play alice bazzaReferenceStrategy) (2 * k) ≤ Real.sqrt 2 := by
            have h_not_win : (play alice bazzaReferenceStrategy) (2 * k) ≤ lam * (2 * k + 1) - s (play alice bazzaReferenceStrategy) (2 * k) := by
              have := ih ( 2 * k ) ( by linarith ) ; unfold ValidMove at this ; aesop;
              unfold s;
              erw [ Finset.sum_Ico_eq_sub _ _ ] at this <;> norm_num at *;
              rw [ Finset.sum_range_succ ] at this ; linarith;
            have h_s_lower_bound : s (play alice bazzaReferenceStrategy) (2 * k) ≥ (k : ℝ) * Real.sqrt 2 := by
              convert lemSLowerBound lam alice ( k + 1 ) ( by linarith ) _ using 1;
              · norm_num;
              · exact fun m hm => ih m ( by omega );
            rw [ lt_div_iff₀ ] at * <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
          unfold q at *;
          norm_num [ Finset.sum_range_succ ];
          nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), show ( play alice bazzaReferenceStrategy ( 2 * k ) : ℝ ) ≥ 0 by positivity ];
        aesop;
        unfold q at *;
        erw [ Finset.sum_Ico_succ_top ] <;> norm_num;
        rw [ show play alice bazzaReferenceStrategy ( 2 * k + 1 ) = bazzaReferenceStrategy k fun i => play alice bazzaReferenceStrategy i from ?_ ];
        · rw [ ← NNReal.coe_le_coe ] ; aesop;
          unfold bazzaReferenceStrategy;
          norm_num [ Finset.sum_range ] at *;
          split_ifs;
          · norm_num [ ← NNReal.coe_le_coe ];
            rw [ Real.sq_sqrt ] <;> linarith;
          · convert h_not_win using 1;
            · unfold bazzaReferenceStrategy;
              norm_num;
            · ring;
        · unfold play;
          norm_num [ Nat.add_mod ];
          rw [ show ( 2 * k + 1 ) / 2 = k by omega ];
          congr!;
          exact?;
    -- By Lemma~\\ref{lem:s_lower_bound}, $S_{2k-2} \\ge (k-1)\\sqrt{2}$ for all $k \\ge 1$.
    have h_s_lower_bound : ∀ k : ℕ, 1 ≤ k → s (play alice bazzaReferenceStrategy) (2 * (k - 1)) ≥ ((k - 1) : ℝ) * Real.sqrt 2 := by
      intro k hk;
      convert lemSLowerBound lam alice k hk _;
      exact fun m hm => h_game_continues m;
    -- Choose $k$ such that $(k-1)\\sqrt{2} > \\lambda(2k-1)$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ ((k - 1) : ℝ) * Real.sqrt 2 > lam * ((2 * k - 1) : ℝ) := by
      rw [ lt_div_iff₀ ] at * <;> norm_num;
      exact ⟨ ⌊ ( 1 - lam * Real.sqrt 2 ) ⁻¹ * 2⌋₊ + 2, by linarith, by push_cast; nlinarith [ Nat.lt_floor_add_one ( ( 1 - lam * Real.sqrt 2 ) ⁻¹ * 2 ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_inv_cancel₀ ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] : ( 1 - lam * Real.sqrt 2 ) ≠ 0 ) ] ⟩;
    specialize h_s_lower_bound k hk.1;
    specialize h_game_continues ( 2 * ( k - 1 ) ) ; unfold ValidMove at h_game_continues ; aesop;
    erw [ Finset.sum_Ico_eq_sub _ _ ] at h_game_continues <;> norm_num at *;
    unfold s at h_s_lower_bound;
    rw [ Finset.sum_range_succ ] at h_game_continues;
    linarith [ show ( play alice bazzaReferenceStrategy ( 2 * ( k - 1 ) ) : ℝ ) ≥ 0 by positivity ];
  exact ⟨ bazzaReferenceStrategy, h_bazza_wins ⟩

/-
If $\\lambda > 1/\\sqrt{2}$, there exists a positive integer $K$ such that $\\lambda > \\frac{K\\sqrt{2}}{2K-1}$.
-/
lemma lemExistenceOfKForAlice (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) :
  ∃ K : ℕ, 1 ≤ K ∧ lam > f K := by
  have := @lemFLimit;
  exact Filter.eventually_atTop.mp ( this.eventually ( gt_mem_nhds hlam ) ) |> fun ⟨ K, hK ⟩ ↦ ⟨ K + 1, by linarith, hK _ <| by linarith ⟩

/-
For Alice's strategy from Definition~\\ref{def:alice_strategy}, the sum $S_{2K-2}$ is bounded by $(S_{2K-2})^2 \\le (K-1)Q_{2K-2}$.
-/
lemma lemSBoundByQ (lam : ℝ) (K : ℕ) (hK : 1 ≤ K) (bazza : BazzaStrategy) :
  let xs := play (aliceReferenceStrategy lam K) bazza
  (s xs (2 * (K - 1))) ^ 2 ≤ ((K - 1) : ℝ) * q xs (2 * (K - 1)) := by
  -- By definition of $s$ and $q$, we can split the sum into two parts: one over even indices and one over odd indices.
  have h_split_sum : s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ∧ q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 := by
    -- By definition of $s$ and $q$, we can split the sum into two parts: one over even indices and one over odd indices. Since Alice's strategy for the first $K-1$ turns is to choose $0$, the sum of the play values at even indices up to $2*(K-1)$ is zero. Therefore, the total sum is just the sum of the play values at the odd indices.
    have h_split_sum : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ∧ ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) ^ 2 = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 := by
      -- By definition of $play$, we know that for even indices, the value is zero, and for odd indices, it's determined by Bazza's strategy.
      have h_play_even_zero : ∀ i < K - 1, play (aliceReferenceStrategy lam K) bazza (2 * i) = 0 := by
        -- By definition of play, for even indices, the value is determined by Alice's strategy. Since Alice's strategy returns zero for indices less than K-1, we have:
        intros i hi
        have h_alice_move : aliceReferenceStrategy lam K i (fun j => play (aliceReferenceStrategy lam K) bazza j) = 0 := by
          unfold aliceReferenceStrategy;
          grind;
        unfold play;
        -- Since $2i$ is even, the play value is determined by Alice's strategy, which returns zero for indices less than $K-1$.
        simp [h_alice_move];
        rwa [ Nat.mul_div_cancel_left _ ( by decide ) ];
      -- By definition of $play$, we know that for even indices, the value is zero, and for odd indices, it's determined by Bazza's strategy. Therefore, we can split the sum into two parts: one over even indices and one over odd indices.
      have h_split_sum : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i) : ℝ) + ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ∧ ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) ^ 2 = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i) : ℝ) ^ 2 + ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 := by
        induction' K - 1 with k hk;
        · norm_num;
        · simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, Finset.sum_range_succ ];
          constructor <;> ring;
      exact ⟨ by rw [ h_split_sum.1, Finset.sum_eq_zero fun i hi => by rw [ h_play_even_zero i ( Finset.mem_range.mp hi ) ] ; norm_num ] ; ring, by rw [ h_split_sum.2, Finset.sum_eq_zero fun i hi => by rw [ h_play_even_zero i ( Finset.mem_range.mp hi ) ] ; norm_num ] ; ring ⟩;
    exact h_split_sum;
  -- Applying the Cauchy-Schwarz inequality to the sums, we get:
  have h_cauchy_schwarz : (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ))^2 ≤ (Finset.card (Finset.range (K - 1))) * (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ)^2) := by
    exact?;
  cases K <;> aesop

/-
If Alice follows her reference strategy, any sequence of valid moves by Bazza up to turn $2K-2$ must satisfy $S_{2K-2} \\le \\sqrt{2}(K-1)$.
-/
lemma lemBazzaDefenseSBound (lam : ℝ) (K : ℕ) (hK : 1 ≤ K) (bazza : BazzaStrategy)
  (h_valid : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) ≤ Real.sqrt 2 * ((K - 1) : ℝ) := by
  -- By the properties of the play sequence and the ValidMove condition, we can derive that the sum of the first 2*(K-1) terms is bounded by sqrt(2)*(K-1).
  have h_sum_bound : (s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) ^ 2 ≤ (K - 1) * q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) := by
    exact?;
  -- Substitute the bound on $q$ into the inequality for $s$.
  have h_subst : (s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) ^ 2 ≤ (K - 1) * (2 * (K - 1)) := by
    specialize h_valid ( 2 * K - 3 ) ; rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
    refine le_trans h_sum_bound ?_;
    unfold q at *;
    rw [ Finset.sum_range_succ ];
    unfold ValidMove at h_valid ; aesop;
    erw [ Finset.sum_Ico_succ_top ] at h_valid <;> norm_num at *;
    exact mul_le_mul_of_nonneg_left ( mod_cast h_valid ) ( by positivity );
  nlinarith only [ show 0 ≤ Real.sqrt 2 * ( K - 1 ) by exact mul_nonneg ( Real.sqrt_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hK ) ), h_subst, Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ]

/-
Alice's move $x_{2K-1}$ in her reference strategy is a valid move.
-/
lemma lemAliceMoveValid (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) (K : ℕ) (hK : 1 ≤ K ∧ lam > f K)
  (bazza : BazzaStrategy)
  (h_valid_hist : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  ValidMove lam (play (aliceReferenceStrategy lam K) bazza) (2 * K - 2) := by
  unfold ValidMove; aesop;
  · -- By definition of $S$, we can write
    have hS : ∑ i in Finset.Iic (2 * K - 2), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = s (play (aliceReferenceStrategy lam K) bazza) (2 * K - 1) := by
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
      rcases K with ( _ | _ | K ) <;> trivial;
    rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    · unfold s;
      unfold play; norm_num;
      unfold aliceReferenceStrategy;
      norm_num;
      split_ifs <;> norm_num ; linarith [ inv_nonneg.2 ( Real.sqrt_nonneg 2 ) ];
    · unfold f at right;
      rw [ div_lt_iff₀ ] at right <;> norm_num at *;
      · have := lemBazzaDefenseSBound lam ( K + 1 + 1 ) ( by linarith ) bazza;
        unfold s at *;
        rw [ Finset.sum_range_succ ];
        rw [ show play ( aliceReferenceStrategy lam ( K + 1 + 1 ) ) bazza ( 2 * K + 2 ) = aliceReferenceStrategy lam ( K + 1 + 1 ) ( K + 1 ) ( fun i => play ( aliceReferenceStrategy lam ( K + 1 + 1 ) ) bazza i ) from ?_ ];
        · unfold aliceReferenceStrategy at *;
          norm_num [ Finset.sum_range, Nat.mul_succ ] at *;
          split_ifs <;> norm_num;
          · linarith!;
          · exact le_trans ( this fun m mn => h_valid_hist m mn ) ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] );
        · unfold play;
          norm_num [ Nat.add_mod ];
          rw [ show ( 2 * K + 2 ) / 2 = K + 1 by norm_num [ Nat.add_div ] ];
          congr!;
          exact?;
      · linarith;
  · exact absurd h ( by rw [ Nat.odd_iff ] ; omega )

/-
Following her reference strategy, Alice wins at turn $2K$ if and only if $\\lambda(2K-1) > S_{2K-2} + \\sqrt{2K - Q_{2K-2}}$.
-/
lemma lemAliceWinConditionFinalForm (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) (K : ℕ) (hK : 1 ≤ K ∧ lam > f K) (bazza : BazzaStrategy)
  (h_valid : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  let xs := play (aliceReferenceStrategy lam K) bazza
  (q xs (2 * K - 1) > (2 * K : ℝ)) ↔
  lam * ((2 * K - 1) : ℝ) > s xs (2 * (K - 1)) + Real.sqrt ((2 * K : ℝ) - q xs (2 * (K - 1))) := by
  bound;
  · -- Since $a > 2K$, we have $q xs (2K-1) > 2K$, which implies $q xs (2(K-1)) + (xs (2K-2))^2 > 2K$.
    have h_q_split : q xs (2 * (K - 1)) + (xs (2 * K - 2) : ℝ) ^ 2 > 2 * K := by
      convert a using 1;
      unfold q;
      rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, Finset.sum_range_succ ];
    -- Substitute $x_{2K-1} = \\lambda(2K-1) - S_{2K-2}$ into the inequality.
    have h_subst : (xs (2 * K - 2) : ℝ) = lam * (2 * K - 1) - s xs (2 * (K - 1)) := by
      have h_subst : xs (2 * K - 2) = aliceReferenceStrategy lam K (K - 1) (fun i => xs i) := by
        have h_subst : ∀ n, xs n = if n % 2 = 0 then aliceReferenceStrategy lam K (n / 2) (fun i => xs i) else bazza (n / 2) (fun i => xs i) := by
          exact?;
        rw [ h_subst ];
        rw [ if_pos ( by omega ), show ( 2 * K - 2 ) / 2 = K - 1 by omega ];
      unfold aliceReferenceStrategy at h_subst;
      rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
      · unfold s; norm_num;
        split_ifs <;> norm_num ; linarith [ inv_nonneg.2 ( Real.sqrt_nonneg 2 ) ];
      · unfold s;
        split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ Finset.sum_range ];
        have := h_valid ( 2 * K + 1 ) ( by linarith ) ; unfold ValidMove at this ; aesop;
        contrapose! h_q_split;
        unfold q;
        norm_cast;
        exact le_trans ( by rw [ Finset.range_eq_Ico ] ; rfl ) ( this.trans ( by ring_nf; norm_num ) );
    aesop;
    -- Taking the square root of both sides of the inequality from h_q_split, we get Real.sqrt (2 * K - q xs (2 * (K - 1))) < lam * (2 * K - 1) - s xs (2 * (K - 1)).
    have h_sqrt : Real.sqrt (2 * K - q xs (2 * (K - 1))) < lam * (2 * K - 1) - s xs (2 * (K - 1)) := by
      rw [ Real.sqrt_lt ];
      · linarith;
      · rcases K with ( _ | _ | K ) <;> norm_num [ Nat.mul_succ ] at *;
        · exact show ( ∑ i in Finset.range 0, ( xs i : ℝ ) ^ 2 ) ≤ 2 by norm_num;
        · specialize h_valid ( 2 * K + 1 ) ; unfold ValidMove at h_valid ; aesop;
          unfold q;
          norm_cast;
          exact le_trans ( by rw [ Finset.range_eq_Ico ] ; rfl ) ( h_valid.trans ( by ring_nf; norm_num ) );
      · exact h_subst ▸ NNReal.coe_nonneg _;
    linarith;
  · -- Substitute the expression for $xs (2K - 2)$ from Alice's reference strategy.
    have h_subst : xs (2 * K - 2) = lam * (2 * K - 1) - s xs (2 * K - 2) := by
      rcases K with ( _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
      -- By definition of \`aliceReferenceStrategy\`, when \`n + 1 = K\`, Alice sets \`xs (2 * K)\` to \`lam * (2 * (K + 1) - 1) - s xs (2 * K)\`.
      have h_alice_move : xs (2 * K) = aliceReferenceStrategy lam (K + 1) K (fun i => xs i) := by
        have h_alice_move : ∀ n, xs n = if n % 2 = 0 then aliceReferenceStrategy lam (K + 1) (n / 2) (fun i => xs i) else bazza (n / 2) (fun i => xs i) := by
          exact?;
        rw [ h_alice_move ] ; norm_num;
        rw [ Nat.mul_div_cancel_left _ ( by decide ) ];
      unfold aliceReferenceStrategy at *;
      unfold s at *;
      simp +zetaDelta at *;
      rw [ h_alice_move, Finset.sum_range ];
      split_ifs <;> norm_num;
      exact False.elim <| ‹¬_› <| by simpa [ Finset.sum_range ] using a.le.trans' <| add_le_add_left ( Real.sqrt_nonneg _ ) _;
    -- Substitute the expression for $q xs (2 * K - 1)$ using the definition of $q$.
    have h_q : q xs (2 * K - 1) = q xs (2 * K - 2) + (xs (2 * K - 2) : ℝ) ^ 2 := by
      unfold q;
      cases K <;> norm_num [ Nat.mul_succ, Finset.sum_range_succ ] at *;
    rcases K with ( _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    contrapose! a;
    nlinarith [ Real.sqrt_nonneg ( 2 * ( K + 1 ) - q xs ( 2 * K ) ), Real.mul_self_sqrt ( show 0 ≤ 2 * ( K + 1 ) - q xs ( 2 * K ) by nlinarith ) ]

/-
For any sequence of valid moves by Bazza against Alice's reference strategy, $S_{2K-2} + \\sqrt{2K - Q_{2K-2}} \\le K\\sqrt{2}$.
-/
lemma lemBazzaObjectiveUpperBound (lam : ℝ) (K : ℕ) (hK : 2 ≤ K) (bazza : BazzaStrategy)
  (h_valid : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  let xs := play (aliceReferenceStrategy lam K) bazza
  s xs (2 * (K - 1)) + Real.sqrt ((2 * K : ℝ) - q xs (2 * (K-1))) ≤ (K : ℝ) * Real.sqrt 2 := by
  -- By Lemma~\\ref{lem:q_bound}, we know that $Q_{2K-2} \\leq 2(K-1)$.
  have h_q_bound : q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) ≤ 2 * (K - 1) := by
    -- Apply the hypothesis \`h_valid\` with \`m = 2 * (K - 1) - 1\`.
    specialize h_valid (2 * (K - 1) - 1);
    rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    unfold ValidMove at h_valid ; aesop;
    convert h_valid using 1;
    unfold q; norm_cast;
    erw [ Finset.range_eq_Ico ] ; rfl;
  -- By Lemma~\\ref{lem:s_lower_bound}, we know that $S_{2K-2} \\leq \\sqrt{(K-1)Q_{2K-2}}$.
  have h_s_lower_bound : s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) ≤ Real.sqrt ((K - 1) * q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) := by
    refine Real.le_sqrt_of_sq_le ?_;
    unfold s q;
    -- By definition of play, we know that play (aliceReferenceStrategy lam K) bazza (2 * i) = 0 for all i < K - 1.
    have h_play_zero : ∀ i < K - 1, play (aliceReferenceStrategy lam K) bazza (2 * i) = 0 := by
      unfold play;
      unfold aliceReferenceStrategy;
      grind;
    -- Since $play (aliceReferenceStrategy lam K) bazza (2 * i) = 0$ for all $i < K - 1$, we can split the sum into two parts: one over even indices and one over odd indices.
    have h_split_sum : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) := by
      have h_split_sum : Finset.range (2 * (K - 1)) = Finset.image (fun i => 2 * i) (Finset.range (K - 1)) ∪ Finset.image (fun i => 2 * i + 1) (Finset.range (K - 1)) := by
        ext ; aesop;
        · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
        · linarith;
      rw [ h_split_sum, Finset.sum_union ];
      · norm_num;
        exact Finset.sum_eq_zero fun i hi => by rw [ h_play_zero i ( Finset.mem_range.mp hi ) ] ; norm_num;
      · norm_num [ Finset.disjoint_right ];
        grind;
    -- Applying the Cauchy-Schwarz inequality to the sum of the terms over odd indices.
    have h_cauchy_schwarz_odd : (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ))^2 ≤ (K - 1) * (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ)^2) := by
      have h_cauchy_schwarz_odd : ∀ (u v : Fin (K - 1) → ℝ), (∑ i, u i * v i)^2 ≤ (∑ i, u i^2) * (∑ i, v i^2) := by
        exact?;
      simpa [ Finset.sum_range, Nat.cast_sub ( show 1 ≤ K by linarith ) ] using h_cauchy_schwarz_odd ( fun _ => 1 ) ( fun i => ( play ( aliceReferenceStrategy lam K ) bazza ( 2 * i + 1 ) : ℝ ) );
    -- Since the play values at even indices are zero, the sum of the squares up to 2*(K-1) is just the sum of the squares of the odd terms up to K-1.
    have h_split_sum_sq : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ)^2 = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ)^2 := by
      have h_split_sum_sq : Finset.range (2 * (K - 1)) = Finset.image (fun i => 2 * i) (Finset.range (K - 1)) ∪ Finset.image (fun i => 2 * i + 1) (Finset.range (K - 1)) := by
        ext ; aesop;
        · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
        · grind;
      rw [ h_split_sum_sq, Finset.sum_union ];
      · norm_num;
        exact Finset.sum_eq_zero fun i hi => by rw [ h_play_zero i ( Finset.mem_range.mp hi ) ] ; norm_num;
      · norm_num [ Finset.disjoint_right ];
        intros; omega;
    aesop;
  refine le_trans ( add_le_add h_s_lower_bound le_rfl ) ?_;
  -- Applying the Cauchy-Schwarz inequality, we get:
  have h_cauchy_schwarz : (Real.sqrt ((K - 1) * q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) + Real.sqrt (2 * K - q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)))) ^ 2 ≤ (K - 1 + 1) * ((q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) + (2 * K - q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)))) := by
    rw [ Real.sqrt_mul ( by norm_num; linarith ) ];
    nlinarith only [ sq_nonneg ( Real.sqrt ( K - 1 ) * Real.sqrt ( 2 * K - q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) ) - Real.sqrt ( q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) ) ), Real.mul_self_sqrt ( show ( K : ℝ ) - 1 ≥ 0 by norm_num; linarith ), Real.mul_self_sqrt ( show ( q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) : ℝ ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => sq_nonneg _ ), Real.mul_self_sqrt ( show ( 2 * K - q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) : ℝ ) ≥ 0 by linarith ) ];
  exact le_trans ( Real.le_sqrt_of_sq_le h_cauchy_schwarz ) ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] ⟩ )

/-
If $\\lambda > 1/\\sqrt{2}$, Alice has a winning strategy.
-/
lemma lemAliceWinsLargeLambda (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) :
  ∃ alice, AliceStrategy.Wins lam alice := by
  -- obtain such a K using lemExistenceOfKForAlice
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 ≤ K ∧ lam > f K := by
    exact?;
  use aliceReferenceStrategy lam K;
  intro bazza;
  by_contra h_contra;
  -- If Alice never wins, then Bazza must win by turn $2K-1$.
  have h_bazza_wins : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m := by
    intro m hm;
    induction' m using Nat.strong_induction_on with m ih;
    by_cases h_even : Even m;
    · unfold ValidMove;
      -- Since $m$ is even, we can write $m = 2k$ for some $k$.
      obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := even_iff_two_dvd.mp h_even;
      -- By definition of play, we can write out the sum.
      have h_sum : ∑ i in Finset.Iic (2 * k), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range k, (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) := by
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
        rw [ show ( Finset.range ( 2 * k ) : Finset ℕ ) = Finset.image ( fun i => 2 * i ) ( Finset.range k ) ∪ Finset.image ( fun i => 2 * i + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num;
        · unfold play;
          unfold aliceReferenceStrategy;
          norm_num;
          rw [ Finset.sum_congr rfl fun i hi => by rw [ if_pos ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show 2 ≤ 2 * K from by linarith ) ] ) ] ] ; norm_num;
          intros; omega;
        · norm_num [ Finset.disjoint_right ];
          intros; omega;
        · ext ; aesop;
          · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
          · linarith;
      -- By definition of play, we can write out the sum of squares.
      have h_sum_squares : ∑ i in Finset.range k, (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 ≤ 2 * k := by
        have := ih ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
        have := ih ( 2 * k + 1 ) ( by linarith ) ( by omega ) ; unfold ValidMove at this; aesop;
        norm_cast;
        refine le_trans ?_ ( this.trans ?_ );
        · have h_sum_squares : Finset.image (fun i => 2 * i + 1) (Finset.range (k + 1)) ⊆ Finset.Iic (2 * k + 1) := by
            exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_Iic.mpr ( by linarith [ Finset.mem_range.mp hi ] );
          exact le_trans ( by rw [ Finset.sum_image ( by norm_num ) ] ) ( Finset.sum_le_sum_of_subset h_sum_squares );
        · norm_cast;
      have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => pow_two_nonneg ( ( play ( aliceReferenceStrategy lam K ) bazza ( 2 * i + 1 ) : ℝ ) - Real.sqrt 2 );
      norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] at this;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
      rw [ inv_eq_one_div, div_lt_iff₀ ] at hlam <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
    · contrapose! h_contra;
      use m;
      exact ⟨ ⟨ h_contra, fun n hn => not_lt.1 fun contra => hn <| ih n contra <| by omega ⟩, Nat.odd_iff.mpr <| Nat.not_even_iff.mp h_even ⟩;
  have h_alice_wins : q (play (aliceReferenceStrategy lam K) bazza) (2 * K - 1) > (2 * K : ℝ) := by
    have h_alice_wins : lam * ((2 * K - 1) : ℝ) > s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) + Real.sqrt ((2 * K : ℝ) - q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) := by
      have := lemBazzaObjectiveUpperBound lam K;
      rcases K with ( _ | _ | K ) <;> aesop;
      · unfold s q; norm_num;
        unfold f at hK ; aesop;
        norm_num at hK ; linarith;
      · refine' lt_of_le_of_lt ( this bazza h_bazza_wins ) _;
        unfold f at hK;
        rw [ div_lt_iff₀ ] at hK <;> norm_num at * <;> nlinarith;
    exact?;
  refine' h_contra ⟨ 2 * K - 1, _, _ ⟩;
  · -- Since $ValidMove$ holds for all $m < 2K-2$, the next $m$ where $ValidMove$ fails must be $2K-1$.
    have h_least : ∀ m, m < 2 * K - 1 → ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m := by
      -- Since $m < 2K-1$, we have either $m < 2K-2$ or $m = 2K-2$. In both cases, $ValidMove$ holds by $h_bazza_wins$.
      intros m hm
      by_cases hm' : m < 2 * K - 2;
      · exact h_bazza_wins m hm';
      · convert lemAliceMoveValid lam hlam K hK bazza _;
        · omega;
        · exact h_bazza_wins;
    refine' ⟨ _, fun m hm => _ ⟩ <;> aesop;
    · unfold ValidMove at a;
      rcases K with ( _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
      unfold q at h_alice_wins;
      erw [ Finset.sum_Ico_succ_top ] at a <;> norm_num at *;
      exact h_alice_wins.not_le ( by norm_num [ ← NNReal.coe_le_coe ] at *; nlinarith );
    · exact not_lt.1 fun contra => hm <| h_least m <| by omega;
  · exact ⟨ K - 1, by omega ⟩

/-
Alice wins if $\\lambda > 1 / \\sqrt{2}$. Bazza wins if $0 < \\lambda < 1 / \\sqrt{2}$.
-/
theorem main_theorem :
  {lam : ℝ | 0 < lam ∧ ∃ alice : AliceStrategy, alice.Wins lam} = {lam : ℝ | 1 / Real.sqrt 2 < lam} ∧
  {lam : ℝ | 0 < lam ∧ ∃ bazza : BazzaStrategy, bazza.Wins lam} = {lam : ℝ | 0 < lam ∧ lam < 1 / Real.sqrt 2} := by
  constructor;
  · apply Set.ext;
    bound;
    · cases a ; aesop;
      -- By definition of Alice's winning strategy, if Alice has a winning strategy, then x must be greater than 1/sqrt(2).
      have h_x_gt : x > 1 / Real.sqrt 2 := by
        have := h bazzaReferenceStrategy;
        -- By definition of Alice's winning strategy, if Alice has a winning strategy, then there exists some $n$ where the move is invalid and $n$ is odd.
        obtain ⟨n, hn₁, hn₂⟩ := this;
        -- By definition of ValidMove, if the move is invalid, then for odd n, the sum of squares exceeds n+1.
        have h_sum_squares : ∑ i in Finset.range n, (play w bazzaReferenceStrategy i : ℝ) ^ 2 > n + 1 := by
          have := hn₁.1;
          unfold ValidMove at this;
          aesop;
          · exact absurd h_1 ( by simpa using hn₂ );
          · contrapose! this;
            erw [ Finset.sum_Ico_succ_top ] <;> norm_num;
            rw [ ← NNReal.coe_le_coe ] ; aesop;
            rw [ show play w bazzaReferenceStrategy n = bazzaReferenceStrategy ( n / 2 ) ( fun i => play w bazzaReferenceStrategy i ) from ?_ ];
            · unfold bazzaReferenceStrategy;
              norm_num [ ← NNReal.coe_le_coe ];
              split_ifs;
              · norm_num [ ← NNReal.coe_le_coe, Finset.sum_range ];
                rw [ Real.sq_sqrt ];
                · rw [ show n = 2 * ( n / 2 ) + 1 by linarith [ Nat.odd_iff.mp hn₂, Nat.div_add_mod n 2 ] ];
                  norm_num [ Nat.add_div ];
                  rw [ show ( 2 * ( n / 2 ) + 1 ) / 2 = n / 2 by omega ] ; linarith;
                · linarith;
              · convert this using 1;
                unfold bazzaReferenceStrategy;
                norm_num;
            · unfold play;
              norm_num [ Nat.odd_iff.mp hn₂ ];
              congr!;
              exact?;
        -- Since $n$ is odd, we can write $n = 2k + 1$ for some $k$.
        obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := hn₂;
        -- By definition of play, we can write out the sum of squares for the first 2k+1 turns.
        have h_play_sum_squares : ∑ i in Finset.range (2 * k + 1), (play w bazzaReferenceStrategy i : ℝ) ^ 2 ≤ 2 * k + (play w bazzaReferenceStrategy (2 * k) : ℝ) ^ 2 := by
          -- By definition of ValidMove, the sum of squares up to 2k is ≤ 2k.
          have h_sum_squares_2k : ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) ^ 2 ≤ 2 * k := by
            have := hn₁.2;
            have := @this ( 2 * k ) ; unfold ValidMove at this ; aesop;
            have := @this_1 ( 2 * k ) ; unfold ValidMove at this ; aesop;
            have := @this_1 ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
            unfold ValidMove at this ; aesop;
            convert NNReal.coe_le_coe.mpr this using 1;
            · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num;
            · norm_cast;
          rw [ Finset.sum_range_succ ] ; linarith;
        have h_play_sum_squares : play w bazzaReferenceStrategy (2 * k) ≤ x * (2 * k + 1) - ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) := by
          have := hn₁.2;
          have := @this ( 2 * k ) ; unfold ValidMove at this ; aesop;
          erw [ Finset.sum_Ico_succ_top ] at this <;> norm_num at *;
          linarith;
        have h_play_sum_squares : ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) ≥ k * Real.sqrt 2 := by
          have := @lemSLowerBound x w ( k + 1 ) ( by linarith ) ?_;
          · aesop;
          · intro m hm;
            have := hn₁.2;
            exact Classical.not_not.1 fun hnm => not_lt_of_ge ( this hnm ) ( by omega );
        simp +zetaDelta at *;
        -- By combining the terms, we can factor out $\\sqrt{2}$ and simplify the expression.
        have h_simplified : Real.sqrt 2 < x * (2 * k + 1) - k * Real.sqrt 2 := by
          nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( play w bazzaReferenceStrategy ( 2 * k ) : ℝ ) ≥ 0 by positivity ];
        rw [ inv_eq_one_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
      simpa using h_x_gt;
    · exact ⟨ lt_trans ( by positivity ) a, lemAliceWinsLargeLambda x a ⟩;
  · -- To prove the equality, we show mutual inclusion.
    apply Set.ext
    intro lam;
    constructor;
    · -- If there exists a bazza strategy that wins, then by the problem's statement, lam must be less than 1/sqrt(2).
      intro h
      obtain ⟨bazza, hbazza⟩ := h.right
      have hlam : 0 < lam ∧ lam < 1 / Real.sqrt 2 := by
        specialize hbazza ( fun n x => 0 );
        aesop;
        unfold ValidMove at *;
        have := left_1.1 ; aesop;
        contrapose! this;
        -- Since $w$ is even, we can write $w = 2k$ for some $k$.
        obtain ⟨k, rfl⟩ : ∃ k, w = 2 * k := even_iff_two_dvd.mp right;
        -- By definition of play, we can write out the sum.
        have h_sum : ∑ i in Finset.Iic (2 * k), (play (fun n x => 0) bazza i : ℝ) = ∑ i in Finset.range k, (play (fun n x => 0) bazza (2 * i + 1) : ℝ) := by
          erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
          rw [ show ( Finset.range ( 2 * k ) : Finset ℕ ) = Finset.image ( fun i => 2 * i ) ( Finset.range k ) ∪ Finset.image ( fun i => 2 * i + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num;
          · unfold play;
            norm_num;
          · norm_num [ Finset.disjoint_right ];
            intros; omega;
          · ext ; aesop;
            · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
            · linarith;
        -- By definition of play, we can write out the sum of squares.
        have h_sum_squares : ∑ i in Finset.range k, (play (fun n x => 0) bazza (2 * i + 1) : ℝ) ^ 2 ≤ 2 * k := by
          have := left_1.2;
          have := @this ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
          convert NNReal.coe_le_coe.mpr this using 1;
          · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
            unfold play;
            exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Nat.mul_succ, Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod ] at * ; linarith;
          · norm_cast;
        have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => pow_two_nonneg ( ( play ( fun n x => 0 ) bazza ( 2 * i + 1 ) : ℝ ) - Real.sqrt 2 );
        norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] at this;
        norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
        rw [ inv_eq_one_div, div_le_iff₀ ] at * <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]
      exact hlam;
    · exact fun h => ⟨ h.1, lemBazzaWinsSmallLambda lam h ⟩

#print axioms main_theorem
`,f=[{label:"General · simp + intro",value:B},{label:"General · rw + exact",value:K},{label:"General · by cases",value:I},{label:"Harmonic · IMO 2025 P1",value:D,imports:["HarmonicLean.Imports"]},{label:"Harmonic · IMO 2025 P3",value:A,imports:["HarmonicLean.Imports"]},{label:"Harmonic · IMO 2025 P4",value:M,imports:["HarmonicLean.Imports"]},{label:"Harmonic · IMO 2025 P5",value:T,imports:["HarmonicLean.Imports"]}],O=`import Mathlib

attribute [simp] Nat.ModEq.refl
`,P=`import HarmonicLean.Attrs
`,V={"HarmonicLean.Attrs":O,"HarmonicLean.Imports":P};function C(){var u,v;const[l,p]=o.useState(((u=f[0])==null?void 0:u.value)??""),[h,$]=o.useState(((v=f[0])==null?void 0:v.imports)??[]),[c,m]=o.useState([]),{mode:y,setMode:x,theme:g}=z(),[i,s]=o.useState("idle"),[w,_]=o.useState(null),N=["LLM output will appear here."],k=["Request in progress."],F=[w??"LLM request failed."],S=c.length>0?c:i==="pending"?k:i==="error"?F:N,L=c.length===0&&i==="idle",q=async()=>{var t;if(!l.trim()){_("Add a Lean proof before requesting the LLM."),s("error");return}const e=h.map(a=>{const r=V[a];return r?{name:a,content:r}:null}).filter(a=>a!==null);s("pending"),_(null),m([]);try{const a=await fetch("/api/explain",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({proof:l,imports:e})});if(!a.ok){const d=await a.text();throw new Error(d||"Request failed.")}const b=(t=(await a.json()).text)==null?void 0:t.trim();if(!b){s("error"),_("No response text returned from the server.");return}m(b.split(`
`).filter(d=>d.trim().length>0)),s("ready")}catch(a){const r=a instanceof Error?a.message:"Request failed.";_(r),s("error")}};return n.jsxs("div",{className:`page theme-${g}`,children:[n.jsx(j,{mode:y,onModeChange:x}),n.jsxs("section",{className:"intro",children:[n.jsx("h1",{children:"TR-001 · Proof Walkthrough Generator"}),n.jsx("p",{children:"Paste a Lean proof or tactic script. The system sends the proof to a LLM (gpt-5-nano) and returns a walkthrough."})]}),n.jsxs("main",{className:"workspace",id:"walkthroughs",children:[n.jsxs("section",{className:"panel",children:[n.jsx("div",{className:"panel-header",children:n.jsxs("div",{children:[n.jsx("h2",{children:"Section A · Lean input"}),n.jsx("p",{children:"Paste a theorem, lemma, or tactic block."})]})}),n.jsx("textarea",{className:"code-input",spellCheck:!1,value:l,onChange:e=>p(e.target.value)}),n.jsx("div",{className:"panel-actions",children:n.jsx("button",{className:"primary-button",onClick:q,disabled:i==="pending",children:"Request LLM Explanation"})}),h.length>0?n.jsxs("div",{className:"callout note",children:[n.jsx("span",{className:"callout-label",children:"NOTE"}),n.jsxs("div",{children:[n.jsx("p",{children:"Imports available to the LLM:"}),n.jsx("ul",{children:h.map(e=>n.jsx("li",{children:e},e))})]})]}):null]}),n.jsxs("section",{className:"panel",children:[n.jsxs("div",{className:"panel-header",children:[n.jsxs("div",{children:[n.jsx("h2",{children:"Section B · LLM response"}),n.jsx("p",{children:"Receive an explanation from a LLM."})]}),n.jsx("span",{className:`status-chip ${i}`,children:i==="ready"?"READY":i==="pending"?"PENDING":i==="error"?"ERROR":"IDLE"})]}),n.jsx("div",{className:"explain-output",children:S.map((e,t)=>n.jsx("p",{className:L?"placeholder":void 0,children:e},`${e}-${t}`))}),n.jsx("div",{className:"panel-footer",children:n.jsx("button",{className:"ghost-button",onClick:()=>{m([]),s("idle"),_(null)},children:"Clear explanation"})})]})]}),n.jsxs("section",{className:"samples",children:[n.jsx("div",{className:"panel-header",children:n.jsxs("div",{children:[n.jsx("h2",{children:"Section C · Sample proofs"}),n.jsx("p",{children:"Select a stored proof block from the registry."})]})}),n.jsxs("div",{className:"table",children:[n.jsxs("div",{className:"table-row table-head",children:[n.jsx("span",{children:"LABEL"}),n.jsx("span",{children:"IMPORTS"}),n.jsx("span",{className:"table-action",children:"LOAD"})]}),f.map(e=>{var t;return n.jsxs("div",{className:"table-row",children:[n.jsx("span",{children:e.label}),n.jsx("span",{children:((t=e.imports)==null?void 0:t.join(", "))??"NONE"}),n.jsx("button",{className:"ghost-button",onClick:()=>{p(e.value),$(e.imports??[])},children:"Load"})]},e.label)})]})]})]})}R(document.getElementById("root")).render(n.jsx(o.StrictMode,{children:n.jsx(C,{})}));
