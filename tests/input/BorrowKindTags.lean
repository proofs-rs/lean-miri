import Miri.Input.Reader.Operations

open Lean Miri Miri.Input Miri.MIR
private def read (kind key tag : String) : Except String BorrowKind := do
  let input := Json.mkObj [("status",.str "supported"),("kind",.str kind),
    (key,Json.mkObj [("$lean_miri_shared_ref",toJson (0 : Nat))])]
  let catalog ← Reader.Catalog.parse (Json.mkObj [("shared_payloads",Json.mkObj [
    ("schema_version",toJson (2 : Nat)),("nodes",.arr #[.str tag,input])])])
  catalog.borrowKind (Json.mkObj [("$lean_miri_shared_ref",toJson (1 : Nat))]) "borrow"
private def check (condition : Bool) (reason : String) : IO Unit :=
  unless condition do throw (IO.userError reason)

def main : IO Unit := do
  -- Pinned exporter borrow_kind_json emits strings for these nested tags.
  for (kind,key,tag,expected) in [
      ("mutable","mutability_kind","default",BorrowKind.Mut .Default),
      ("mutable","mutability_kind","two_phase",BorrowKind.Mut .TwoPhaseBorrow),
      ("mutable","mutability_kind","closure_capture",BorrowKind.Mut .ClosureCapture),
      ("fake","fake_kind","shallow",BorrowKind.Fake .Shallow),
      ("fake","fake_kind","deep",BorrowKind.Fake .Deep)] do
    match read kind key tag with
    | .ok actual => check (decide (actual = expected)) s!"borrow tag changed: {kind}/{tag}"
    | .error reason => throw (IO.userError reason)
  check (!(read "mutable" "mutability_kind" "unknown").isOk) "unknown mutable borrow was accepted"
  check (!(read "fake" "fake_kind" "unknown").isOk) "unknown fake borrow was accepted"
  IO.println "pinned borrow enum string tags through shared refs: PASS"
