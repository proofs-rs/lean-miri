import Miri.Concurrency.WeakMemoryVerification

open Miri.Concurrency

def idx (value : Nat) (bound : value < 4294967296) : VectorIdx :=
  VectorIdx.ofU32 value bound

def i0 : VectorIdx := idx 0 (by decide)
def i1 : VectorIdx := idx 1 (by decide)
def i2 : VectorIdx := idx 2 (by decide)

def stamp (time : Nat) (bound : 2 * time < 4294967296) : VTimestamp :=
  VTimestamp.ofPacked (2 * time) bound

def t0 : VTimestamp := stamp 0 (by decide)
def t1 : VTimestamp := stamp 1 (by decide)
def t2 : VTimestamp := stamp 2 (by decide)
def t4 : VTimestamp := stamp 4 (by decide)

def clockAt (index : VectorIdx) (timestamp : VTimestamp) : VClock :=
  VClock.newWithIndex index timestamp

def threadAt (index : VectorIdx) (timestamp : VTimestamp) : ThreadClockSet :=
  { ThreadClockSet.default with clock := clockAt index timestamp }

def baseBuffer : StoreBuffer Nat :=
  let initial := StoreBuffer.new (some 0)
  let one := StoreBuffer.storeImpl initial 1 i0 (clockAt i0 t1) false .default
  StoreBuffer.storeImpl one 2 i0 (clockAt i0 t2) false .default

def markValueSeqCst (buffer : StoreBuffer Nat) (value : Nat) : StoreBuffer Nat :=
  let mark := fun element =>
    if element.val == some value then { element with isSeqCst := true } else element
  { buffer with
    oldest := mark buffer.oldest
    newer := buffer.newer.map mark
    bounded := by simpa using buffer.bounded }

def markValueLoaded (buffer : StoreBuffer Nat) (value : Nat) (loadIndex : VectorIdx)
    (timestamp : VTimestamp) (isSeqCst : Bool) : StoreBuffer Nat :=
  let mark := fun element =>
    if element.val == some value then
      { element with loadInfo :=
          { timestamps := [(loadIndex, timestamp)], scLoaded := isSeqCst } }
    else element
  { buffer with
    oldest := mark buffer.oldest
    newer := buffer.newer.map mark
    bounded := by simpa using buffer.bounded }

def valueCode : Option Nat → String
  | none => "U"
  | some value => toString value

def recencyCode : LoadRecency → String
  | .Latest => "L"
  | .Outdated => "O"

def choiceCode (choice : StoreBuffer.LoadChoice Nat) : String :=
  valueCode choice.element.val ++ recencyCode choice.recency ++ "@" ++
    toString (choice.element.syncClock.index i1).packedValue ++ ":" ++
    toString (choice.element.syncClock.index i2).packedValue

def choicesCode (buffer : StoreBuffer Nat) (isSeqCst : Bool)
    (thread : ThreadClockSet) : String :=
  String.intercalate "," ((StoreBuffer.fetchChoices buffer isSeqCst thread).map choiceCode)

def addStores : Nat → StoreBuffer Nat → StoreBuffer Nat
  | 0, buffer => buffer
  | count + 1, buffer =>
      let value := count + 1
      let prior := addStores count buffer
      StoreBuffer.storeImpl prior value i0 (clockAt i0 t1) false .default
termination_by count _buffer => count
decreasing_by omega

def singleStoreTime (buffer : StoreBuffer Nat) (value : Nat) : Option Nat :=
  match buffer.entries.find? (fun element => element.val == some value) with
  | none => none
  | some element => some element.storeTimestamp.time

def main : IO Unit := do
  IO.println s!"choices:all:{choicesCode baseBuffer false .default}"

  let (rmwBuffer, rmwValue) ← match StoreBuffer.readFromLastStore baseBuffer i1
      (threadAt i1 t2) true with
    | .error _ => throw (IO.userError "RMW latest-store read failed")
    | .ok result => pure result
  let rmwElement := rmwBuffer.entries.find?
    (fun element => element.val == some 2)
  let rmwTimestamp := match rmwElement with
    | none => "missing"
    | some element => match element.loadInfo.timestampFor? i1 with
      | none => "missing"
      | some timestamp => toString timestamp.time
  let rmwScLoaded := match rmwElement with
    | none => false
    | some element => element.loadInfo.scLoaded
  IO.println s!"rmw-last:{valueCode rmwValue}:{rmwTimestamp}:{if rmwScLoaded then 1 else 0}"

  let syncOne := StoreBuffer.storeImpl (StoreBuffer.new (some 0)) 1 i0
    (clockAt i0 t1) false (clockAt i1 t1)
  let syncTwo := StoreBuffer.storeImpl syncOne 2 i0
    (clockAt i0 t2) false (clockAt i2 t2)
  IO.println s!"choices:sync-clocks:{choicesCode syncTwo false .default}"

  let coWr := threadAt i0 t1
  IO.println s!"choices:cowr:{choicesCode baseBuffer false coWr}"

  let coRrBuffer := markValueLoaded baseBuffer 1 i1 t1 false
  let coRrThread := threadAt i1 t1
  IO.println s!"choices:corr:{choicesCode coRrBuffer false coRrThread}"

  let writeScBuffer := markValueSeqCst baseBuffer 1
  let writeScThread := { ThreadClockSet.default with writeSeqCst := clockAt i0 t1 }
  IO.println s!"choices:write-sc:{choicesCode writeScBuffer false writeScThread}"

  let readScThread := { ThreadClockSet.default with readSeqCst := clockAt i0 t1 }
  IO.println s!"choices:read-sc:{choicesCode baseBuffer true readScThread}"

  let scLoadedBuffer := markValueLoaded baseBuffer 1 i1 t0 true
  IO.println s!"choices:sc-loaded:{choicesCode scLoadedBuffer true .default}"

  let sc1 := StoreBuffer.storeImpl (StoreBuffer.new (some 0)) 1 i0
    (clockAt i0 t1) false .default
  let sc2 := StoreBuffer.storeImpl sc1 2 i1 (clockAt i1 t1) true .default
  let sc3 := StoreBuffer.storeImpl sc2 3 i2 (clockAt i2 t1) true .default
  IO.println s!"choices:sc-filter:{choicesCode sc3 true .default}"

  let loadIndex := i1
  let firstClocks := threadAt i1 t2
  let secondClocks := threadAt i1 t4
  let validateFirst : VClock → Except String ThreadClockSet :=
    fun _sync => Except.ok firstClocks
  let validateSecond : VClock → Except String ThreadClockSet :=
    fun _sync => Except.ok secondClocks
  let firstRead ← match StoreBuffer.bufferedReadAt baseBuffer false .default
      loadIndex 1 validateFirst with
    | .error _ => throw (IO.userError "first controlled load failed")
    | .ok result => pure result
  let secondRead ← match StoreBuffer.bufferedReadAt firstRead.buffer true .default
      loadIndex 1 validateSecond with
    | .error _ => throw (IO.userError "second controlled load failed")
    | .ok result => pure result
  let loadedElement := secondRead.buffer.entries.find?
    (fun element => element.val == some 1)
  let firstTimestamp := match loadedElement with
    | none => "missing"
    | some element => match element.loadInfo.timestampFor? loadIndex with
      | none => "missing"
      | some timestamp => toString timestamp.time
  let scLoaded := match loadedElement with
    | none => false
    | some element => element.loadInfo.scLoaded
  IO.println s!"load-info:first:{firstTimestamp}:sc:{if scLoaded then 1 else 0}"

  let validateSync : VClock → Except String ThreadClockSet := fun sync =>
    Except.ok { ThreadClockSet.default with clock := sync }
  let selectedLatest ← match StoreBuffer.bufferedReadAt syncTwo false .default
      loadIndex 0 validateSync with
    | .error _ => throw (IO.userError "latest sync-clock read failed")
    | .ok result => pure result
  let selectedOlder ← match StoreBuffer.bufferedReadAt syncTwo false .default
      loadIndex 1 validateSync with
    | .error _ => throw (IO.userError "outdated sync-clock read failed")
    | .ok result => pure result
  if (selectedLatest.clocks.clock.index i2).packedValue != 4 ||
      (selectedOlder.clocks.clock.index i1).packedValue != 2 then
    throw (IO.userError "buffered read did not pass the chosen store clock to validation")

  let limited := addStores 140 (StoreBuffer.new (some 0))
  let firstValue := match limited.entries.head? with
    | none => "empty"
    | some element => valueCode element.val
  let lastValue := valueCode limited.last.val
  IO.println s!"limit:{limited.entries.length}:{firstValue}:{lastValue}:{STORE_BUFFER_LIMIT}"

  if STORE_BUFFER_LIMIT != 128 then throw (IO.userError "wrong store-buffer cap")
  if choicesCode (StoreBuffer.new (some 7)) false .default != "7L@0:0" then
    throw (IO.userError "initial store must remain a legal latest choice")
