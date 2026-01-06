/-! ## Imperative DSL (macros) -/

declare_syntax_cat impInt
declare_syntax_cat impBool
declare_syntax_cat impStmt

macro:max "v[" n:num "]" : term => `(Fin.ofNat _ $n)

syntax:max num : impInt
syntax:max "-" num : impInt
syntax:max "v[" num "]" : impInt
syntax:max "(" impInt ")" : impInt
syntax:70 impInt:71 " + " impInt:70 : impInt
syntax:80 num " * " impInt:80 : impInt

syntax:max "(" impBool ")" : impBool
syntax:50 impInt:51 " < " impInt:50 : impBool

syntax:max "skip" : impStmt
syntax:max "{" impStmt "}" : impStmt
syntax:35 impStmt:36 " ; " impStmt:35 : impStmt
syntax:40 term " := " impInt : impStmt
syntax:max "if " impBool " then " impStmt " else " impStmt : impStmt
syntax:max "if " impBool " then " impStmt : impStmt
syntax:max "while " impBool " do " impStmt : impStmt

syntax "iexpr| " impInt : term
syntax "bexpr| " impBool : term
syntax "stmt| " impStmt : term

macro_rules
  | `(iexpr| $n:num) => `(.literalInt (Int.ofNat $n))
  | `(iexpr| - $n:num) => `(.literalInt (Int.negOfNat $n))
  | `(iexpr| v[$n:num]) => `(.var (v[$n]))
  | `(iexpr| ($e:impInt)) => `(iexpr| $e)
  | `(iexpr| $e₁:impInt + $e₂:impInt) => `(.add (iexpr| $e₁) (iexpr| $e₂))
  | `(iexpr| $k:num * $e:impInt) => `(.scaleConstant $k (iexpr| $e))

macro_rules
  | `(bexpr| ($b:impBool)) => `(bexpr| $b)
  | `(bexpr| $e₁:impInt < $e₂:impInt) => `(.lessThan (iexpr| $e₁) (iexpr| $e₂))

macro_rules
  | `(stmt| skip) => `(.skip)
  | `(stmt| {$s:impStmt}) => `(stmt| $s)
  | `(stmt| $s₁:impStmt ; $s₂:impStmt) => `(.sequence (stmt| $s₁) (stmt| $s₂))
  | `(stmt| $x:term := $e:impInt) => `(.assign $x (iexpr| $e))
  | `(stmt| if $c:impBool then $t:impStmt else $e:impStmt) =>
      `(.ifThenElse (bexpr| $c) (stmt| $t) (stmt| $e))
  | `(stmt| if $c:impBool then $t:impStmt) =>
      `(.ifThenElse (bexpr| $c) (stmt| $t) .skip)
  | `(stmt| while $c:impBool do $body:impStmt) =>
      `(.whileLoop (bexpr| $c) (stmt| $body))
