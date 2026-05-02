-- Core module for LOUVRE.

namespace LOUVRE

inductive Matcher : Type where
  | literal   : String → Matcher
  | prefix    : String → Matcher
  | contains  : String → Matcher
  | anyOf     : List Matcher → Matcher
  | allOf     : List Matcher → Matcher
  | never     : Matcher
  | always    : Matcher
  deriving Repr, Inhabited

-- checks whether the first list is a prefix of the second list
@[inline] def listIsPrefixOf : List Char → List Char → Bool
  | [], _              => true
  | _ :: _, []         => false
  | x :: xs, y :: ys   => x == y && listIsPrefixOf xs ys

-- checks whether the needle is a contiguous substring of the haystack
def listHasSubstr (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | h@(_ :: rest) => listIsPrefixOf needle h || listHasSubstr needle rest

-- substring check at the `String` level
def hasSubstr (haystack needle : String) : Bool :=
  listHasSubstr needle.toList haystack.toList

-- string prefix check via list traversal, kernel-reducible
def stringIsPrefixOf (p s : String) : Bool :=
  listIsPrefixOf p.toList s.toList

mutual
  -- decides whether a matcher accepts a whole string through mutually recursive helpers
  def accepts : Matcher → String → Bool
    | .literal t,   s => s == t
    | .prefix p,    s => stringIsPrefixOf p s
    | .contains c,  s => hasSubstr s c
    | .anyOf ms,    s => acceptsAny ms s
    | .allOf ms,    s => acceptsAll ms s
    | .never,       _ => false
    | .always,      _ => true
  def acceptsAny : List Matcher → String → Bool
    | [],      _ => false
    | m :: ms, s => accepts m s || acceptsAny ms s
  def acceptsAll : List Matcher → String → Bool
    | [],      _ => true
    | m :: ms, s => accepts m s && acceptsAll ms s
end

-- a prop-valued predicate over strings as the language of a matcher
@[reducible] def language (m : Matcher) (s : String) : Prop := accepts m s = true

-- defining a redaction policy
structure RedactionPolicy where
  source       : Matcher -- the source class of secrets
  matcher      : Matcher -- the matcher that should subsume it
  replacement  : String -- the replacement string for any matched field
  deriving Repr, Inhabited

-- empty fields (from consecutive spaces) are dropped
def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

-- reassembles fields with single-space separators
def unfields (fs : List String) : String :=
  String.intercalate " " fs

-- applies a policy by replacing every whitespace-delimited field that matches the policy's `matcher` with the `replacement`
def redact (p : RedactionPolicy) (s : String) : String :=
  unfields ((fields s).map fun f => if accepts p.matcher f then p.replacement else f)

-- a string contains a secret iff some whitespace-delimited field of it is in the source class
def containsSecret (src : Matcher) (s : String) : Bool :=
  (fields s).any (accepts src)

-- whether a single field is in the source class (Prop form)
def fieldIsSecret (src : Matcher) (f : String) : Prop := accepts src f = true

end LOUVRE
