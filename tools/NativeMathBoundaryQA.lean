import Miri.Input.NativeMathHost

open Miri.Interpreter

private def requireBits (name : String) (expected actual : Math.HostBits) : IO Unit := do
  unless expected == actual do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def binary (op : Math.Binary) (left right : Math.HostBits) : IO Math.HostBits := do
  let host := Miri.Input.NativeMathHost.host Unit Unit
  match (host.binary () op left right).run () with
  | .ok value _ => pure value
  | .error error _ => throw (IO.userError s!"binary callback: {reprStr error}")

private def unary (op : Math.Unary) (value : Math.HostBits) : IO Math.HostBits := do
  let host := Miri.Input.NativeMathHost.host Unit Unit
  match (host.unary () op value).run () with
  | .ok result _ => pure result
  | .error error _ => throw (IO.userError s!"unary callback: {reprStr error}")

private def lgamma (value : Math.HostBits) : IO (Math.HostBits × Int32) := do
  let host := Miri.Input.NativeMathHost.host Unit Unit
  match (host.lgamma () value).run () with
  | .ok result _ => pure result
  | .error error _ => throw (IO.userError s!"lgamma callback: {reprStr error}")

def main : IO Unit := do
  let f32Zero : Math.HostBits := .single (BitVec.ofNat 32 0)
  let f32One : Math.HostBits := .single (BitVec.ofNat 32 0x3f800000)
  let f32Three : Math.HostBits := .single (BitVec.ofNat 32 0x40400000)
  let f32Four : Math.HostBits := .single (BitVec.ofNat 32 0x40800000)
  let f32Five : Math.HostBits := .single (BitVec.ofNat 32 0x40a00000)
  let f64Zero : Math.HostBits := .double (BitVec.ofNat 64 0)
  let f64One : Math.HostBits := .double (BitVec.ofNat 64 0x3ff0000000000000)
  let f64Three : Math.HostBits := .double (BitVec.ofNat 64 0x4008000000000000)
  let f64Four : Math.HostBits := .double (BitVec.ofNat 64 0x4010000000000000)
  let f64Five : Math.HostBits := .double (BitVec.ofNat 64 0x4014000000000000)
  requireBits "hypotf(3,4)" f32Five (← binary .hypot f32Three f32Four)
  requireBits "hypot(3,4)" f64Five (← binary .hypot f64Three f64Four)
  requireBits "sinf(0)" f32Zero (← unary .sin f32Zero)
  requireBits "sin(0)" f64Zero (← unary .sin f64Zero)
  let (f32Gamma, f32Sign) ← lgamma f32One
  requireBits "lgammaf_r(1)" f32Zero f32Gamma
  unless f32Sign == 1 do throw (IO.userError s!"lgammaf_r sign={f32Sign}")
  let (f64Gamma, f64Sign) ← lgamma f64One
  requireBits "lgamma_r(1)" f64Zero f64Gamma
  unless f64Sign == 1 do throw (IO.userError s!"lgamma_r sign={f64Sign}")
  IO.println "source162 native math C ABI: f32/f64 hypot, sin, lgamma value/sign PASS"
