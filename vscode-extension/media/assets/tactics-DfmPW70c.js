import{u as t,j as e,S as r,c as o,r as l}from"./index-CmsUpJRH.js";const c=[{name:"induction",description:"Split a goal into base and inductive cases on a natural number or inductive type.",example:`theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Nat.add_succ, ih]`},{name:"cases",description:"Perform case analysis on a value of an inductive type.",example:`lemma bool_or (p q : Bool) : p || q = true := by
  cases p <;> cases q <;> decide`},{name:"simp",description:"Simplify the goal using rewrite rules and simp lemmas.",example:`example (n : Nat) : n + 0 = n := by
  simp`},{name:"rw",description:"Rewrite the goal using an equality or lemma.",example:`example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]`},{name:"use",description:"Provide a witness for an existential goal.",example:`example : ∃ n : Nat, n = n := by
  use 0
  rfl`},{name:"choose",description:"Extract witnesses and properties from an existence proof.",example:`example (h : ∃ n : Nat, n = n) : True := by
  choose n hn using h
  exact True.intro`},{name:"intro",description:"Introduce a hypothesis or variable into the context.",example:`example (P Q : Prop) : P → Q → P := by
  intro hp hq
  exact hp`},{name:"exact",description:"Close the goal with an exact proof term.",example:`example (P : Prop) (hp : P) : P := by
  exact hp`},{name:"specialize",description:"Apply a hypothesis to specific arguments, creating a more concrete statement.",example:`example (P : Nat → Prop) (h : ∀ n, P n) : P 3 := by
  specialize h 3
  exact h`},{name:"linarith",description:"Solve linear arithmetic goals using linear inequalities.",example:`example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by
  linarith`},{name:"ring_nf",description:"Normalize ring expressions to a canonical form.",example:`example (x y : Nat) : x + y + x = 2 * x + y := by
  ring_nf`},{name:"omega",description:"Solve Presburger arithmetic goals over natural numbers and integers.",example:`example (a b : Nat) : a + b = b + a := by
  omega`},{name:"simp?",description:"Suggest a minimal simp lemma set that proves the goal, then prints a `simp [..]` you can paste.",example:`example (n : Nat) : n + 0 = n := by
  simp?`},{name:"aesop",description:"Search for a proof using a configurable set of rules and tactics.",example:`example (P Q : Prop) : P → Q → P := by
  aesop`},{name:"by_cases",description:"Split the proof into cases based on a decidable proposition.",example:`example (P : Prop) [Decidable P] : P ∨ ¬ P := by
  by_cases hP : P
  · exact Or.inl hP
  · exact Or.inr hP`},{name:"by_contra",description:"Switch to proving false under the assumption that the goal is false.",example:`example (P : Prop) : ¬¬P → P := by
  intro h
  by_contra hP
  exact h hP`}],p=()=>{const{mode:n,setMode:s,theme:i}=t();return e.jsxs("div",{className:`page theme-${i}`,children:[e.jsx(r,{mode:n,onModeChange:s}),e.jsxs("section",{className:"intro",children:[e.jsx("h1",{children:"TR-002 · Tactic Reference"}),e.jsx("p",{children:"Common Lean tactics with short explanations and minimal examples."})]}),e.jsxs("section",{className:"samples",children:[e.jsx("div",{className:"panel-header",children:e.jsxs("div",{children:[e.jsx("h2",{children:"Section A · Tactics"}),e.jsx("p",{children:"Scan by name, then copy a minimal example."})]})}),e.jsxs("div",{className:"table table-tactics",children:[e.jsxs("div",{className:"table-row table-head",children:[e.jsx("span",{children:"TACTIC"}),e.jsx("span",{children:"SUMMARY"}),e.jsx("span",{children:"EXAMPLE"})]}),c.map(a=>e.jsxs("div",{className:"table-row",children:[e.jsx("span",{children:a.name}),e.jsx("span",{children:a.description}),e.jsx("pre",{children:a.example})]},a.name))]})]})]})};o(document.getElementById("root")).render(e.jsx(l.StrictMode,{children:e.jsx(p,{})}));
