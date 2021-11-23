
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}



// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;


// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true of the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true of the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// Note that *not* inlining the shl/shr functions avoids timeouts. It appears that Z3 can reason
// better about this if it is an axiomatized function.
function $shl(src1: int, p: int): int {
    if p == 8 then src1 * 256
    else if p == 16 then src1 * 65536
    else if p == 32 then src1 * 4294967296
    else if p == 64 then src1 * 18446744073709551616
    // Value is undefined, otherwise.
    else -1
}

function $shr(src1: int, p: int): int {
    if p == 8 then src1 div 256
    else if p == 16 then src1 div 65536
    else if p == 32 then src1 div 4294967296
    else if p == 64 then src1 div 18446744073709551616
    // Value is undefined, otherwise.
    else -1
}

// TODO: fix this and $Shr to drop bits on overflow. Requires $Shl8, $Shl64, and $Shl128
procedure {:inline 1} $Shl(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    res := $shl(src1, src2);
    assert res >= 0;   // restriction: shift argument must be 8, 16, 32, or 64
    dst := res;
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    res := $shr(src1, src2);
    assert res >= 0;   // restriction: shift argument must be 8, 16, 32, or 64
    dst := res;
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_Vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_Vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_Vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_Vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_Vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_Vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_Vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_Vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_Vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_Vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_Vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_Vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_Vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_Vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_Vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_Vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_Vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_Hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_Hash_sha2(v1), $1_Hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_Hash_sha2(v1), $1_Hash_sha2(v2)));

procedure $1_Hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_Hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_Hash_$sha2_256(val: Vec int): Vec int {
    $1_Hash_sha2(val)
}

// similarly for Hash_sha3
function $1_Hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_Hash_sha3(v1), $1_Hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_Hash_sha3(v1), $1_Hash_sha3(v2)));

procedure $1_Hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_Hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_Hash_$sha3_256(val: Vec int): Vec int {
    $1_Hash_sha3(val)
}

// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_Signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_Signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_Signer_is_txn_signer(s: $signer): bool;

function $1_Signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native BCS::serialize


// ==================================================================================
// Native Event module




// Generic code for dealing with mutations (havoc) still requires type and memory declarations.
type $1_Event_EventHandleGenerator;
var $1_Event_EventHandleGenerator_$memory: $Memory $1_Event_EventHandleGenerator;

// Abstract type of event handles.
type $1_Event_EventHandle;

// Global state to implement uniqueness of event handles.
var $1_Event_EventHandles: [$1_Event_EventHandle]bool;

// Universal representation of an an event. For each concrete event type, we generate a constructor.
type {:datatype} $EventRep;

// Representation of EventStore that consists of event streams.
type {:datatype} $EventStore;
function {:constructor} $EventStore(
    counter: int, streams: [$1_Event_EventHandle]Multiset $EventRep): $EventStore;

// Global state holding EventStore.
var $es: $EventStore;

procedure {:inline 1} $InitEventStore() {
    assume $EventStore__is_empty($es);
}

function {:inline} $EventStore__is_empty(es: $EventStore): bool {
    (counter#$EventStore(es) == 0) &&
    (forall handle: $1_Event_EventHandle ::
        (var stream := streams#$EventStore(es)[handle];
        IsEmptyMultiset(stream)))
}

// This function returns (es1 - es2). This function assumes that es2 is a subset of es1.
function {:inline} $EventStore__subtract(es1: $EventStore, es2: $EventStore): $EventStore {
    $EventStore(counter#$EventStore(es1)-counter#$EventStore(es2),
        (lambda handle: $1_Event_EventHandle ::
        SubtractMultiset(
            streams#$EventStore(es1)[handle],
            streams#$EventStore(es2)[handle])))
}

function {:inline} $EventStore__is_subset(es1: $EventStore, es2: $EventStore): bool {
    (counter#$EventStore(es1) <= counter#$EventStore(es2)) &&
    (forall handle: $1_Event_EventHandle ::
        IsSubsetMultiset(
            streams#$EventStore(es1)[handle],
            streams#$EventStore(es2)[handle]
        )
    )
}

procedure {:inline 1} $EventStore__diverge(es: $EventStore) returns (es': $EventStore) {
    assume $EventStore__is_subset(es, es');
}

const $EmptyEventStore: $EventStore;
axiom $EventStore__is_empty($EmptyEventStore);

// ----------------------------------------------------------------------------------
// Native Event implementation for element type `$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent`

// Map type specific handle to universal one.
type $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent' = $1_Event_EventHandle;

function {:inline} $IsEqual'$1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent''(a: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent', b: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'): bool {
    a == b
}

function $IsValid'$1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent''(h: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'): bool {
    true
}

// Embed event `$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent` into universal $EventRep
function {:constructor} $ToEventRep'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(e: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent): $EventRep;
axiom (forall v1, v2: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent :: {$ToEventRep'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(v1), $ToEventRep'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(v2)}
    $IsEqual'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(v1, v2) <==> $ToEventRep'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(v1) == $ToEventRep'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(v2));

// Creates a new event handle. This ensures each time it is called that a unique new abstract event handler is
// returned.
// TODO: we should check (and abort with the right code) if no generator exists for the signer.
procedure {:inline 1} $1_Event_new_event_handle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(signer: $signer) returns (res: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent') {
    assume $1_Event_EventHandles[res] == false;
    $1_Event_EventHandles := $1_Event_EventHandles[res := true];
}

// This boogie procedure is the model of `emit_event`. This model abstracts away the `counter` behavior, thus not
// mutating (or increasing) `counter`.
procedure {:inline 1} $1_Event_emit_event'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(handle_mut: $Mutation $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent', msg: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent)
returns (res: $Mutation $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent') {
    var handle: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent';
    handle := $Dereference(handle_mut);
    $es := $ExtendEventStore'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'($es, handle, msg);
    res := handle_mut;
}

procedure {:inline 1} $1_Event_destroy_handle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(handle: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent') {
}

function {:inline} $ExtendEventStore'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(
        es: $EventStore, handle: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent', msg: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent): $EventStore {
    (var stream := streams#$EventStore(es)[handle];
    (var stream_new := ExtendMultiset(stream, $ToEventRep'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(msg));
    $EventStore(counter#$EventStore(es)+1, streams#$EventStore(es)[handle := stream_new])))
}

function {:inline} $CondExtendEventStore'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(
        es: $EventStore, handle: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent', msg: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent, cond: bool): $EventStore {
    if cond then
        $ExtendEventStore'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(es, handle, msg)
    else
        es
}




//==================================
// Begin Translation



// Given Types for Type Parameters


// fun Signer::address_of [baseline] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:12:5+77
procedure {:inline 1} $1_Signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:12:5+1
    assume {:print "$at(17,389,390)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // $t1 := Signer::borrow_address($t0) on_abort goto L2 with $t2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:13:10+17
    assume {:print "$at(17,443,460)"} true;
    call $t1 := $1_Signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(17,443,460)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(0,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:13:9+18
    assume {:print "$track_return(0,0,0):", $t1} $t1 == $t1;

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:14:5+1
    assume {:print "$at(17,465,466)"} true;
L1:

    // return $t1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:14:5+1
    $ret0 := $t1;
    return;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:14:5+1
L2:

    // abort($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/../stdlib/sources/Signer.move:14:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct ERC20::Balance at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:19:5+49
type {:datatype} $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance;
function {:constructor} $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance($coin: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin): $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance;
function {:inline} $Update'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'_coin(s: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance, x: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin): $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance {
    $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance(x)
}
function $IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'(s: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance): bool {
    $IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin'($coin#$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance(s))
}
function {:inline} $IsEqual'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'(s1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance, s2: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance): bool {
    s1 == s2
}
var $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory: $Memory $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance;

// struct ERC20::Coin at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:14:5+48
type {:datatype} $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
function {:constructor} $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($value: int): $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
function {:inline} $Update'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin'_value(s: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin, x: int): $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin {
    $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin(x)
}
function $IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin'(s: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin): bool {
    $IsValid'u64'($value#$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin(s))
}
function {:inline} $IsEqual'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin'(s1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin, s2: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin): bool {
    s1 == s2
}

// struct ERC20::TotalSupply at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:25:5+54
type {:datatype} $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply;
function {:constructor} $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply($supply: int): $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply;
function {:inline} $Update'$24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply'_supply(s: $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply, x: int): $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply {
    $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply(x)
}
function $IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply'(s: $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply): bool {
    $IsValid'u64'($supply#$24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply(s))
}
function {:inline} $IsEqual'$24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply'(s1: $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply, s2: $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply): bool {
    s1 == s2
}
var $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply_$memory: $Memory $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply;

// fun ERC20::balance_of [baseline] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:50:5+116
procedure {:inline 1} $24163afcc6e33b0a9473852e18327fa9_ERC20_balance_of(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance;
    var $t2: int;
    var $t3: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[owner]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:50:5+1
    assume {:print "$at(3,1666,1667)"} true;
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<ERC20::Balance>($t0) on_abort goto L2 with $t2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+13
    assume {:print "$at(3,1736,1749)"} true;
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(3,1736,1749)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<ERC20::Balance>.coin($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+34
    $t3 := $coin#$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance($t1);

    // $t4 := get_field<ERC20::Coin>.value($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+40
    $t4 := $value#$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t3);

    // trace_return[0]($t4) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+40
    assume {:print "$track_return(2,0,0):", $t4} $t4 == $t4;

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
    assume {:print "$at(3,1781,1782)"} true;
L1:

    // return $t4 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
    $ret0 := $t4;
    return;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
L2:

    // abort($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun ERC20::balance_of [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:50:5+116
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_ERC20_balance_of$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance;
    var $t2: int;
    var $t3: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:50:5+1
    assume {:print "$at(3,1666,1667)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: ResourceDomain<ERC20::Balance>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:50:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'($rsc))));

    // trace_local[owner]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:50:5+1
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<ERC20::Balance>($t0) on_abort goto L2 with $t2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+13
    assume {:print "$at(3,1736,1749)"} true;
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(3,1736,1749)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<ERC20::Balance>.coin($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+34
    $t3 := $coin#$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance($t1);

    // $t4 := get_field<ERC20::Coin>.value($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+40
    $t4 := $value#$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t3);

    // trace_return[0]($t4) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:51:9+40
    assume {:print "$track_return(2,0,0):", $t4} $t4 == $t4;

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
    assume {:print "$at(3,1781,1782)"} true;
L1:

    // return $t4 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
    $ret0 := $t4;
    return;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
L2:

    // abort($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:52:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun ERC20::deposit [baseline] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+300
procedure {:inline 1} $24163afcc6e33b0a9473852e18327fa9_ERC20_deposit(_$t0: int, _$t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $temp_0'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin': $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $temp_0'address': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[_addr]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+1
    assume {:print "$at(3,2867,2868)"} true;
    assume {:print "$track_local(2,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+1
    assume {:print "$track_local(2,1,1):", $t1} $t1 == $t1;

    // $t3 := unpack ERC20::Coin($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:79:13+23
    assume {:print "$at(3,2997,3020)"} true;
    $t3 := $value#$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t1);

    // destroy($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:79:27+7

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:84:5+1
    assume {:print "$at(3,3166,3167)"} true;
L1:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:84:5+1
    return;

}

// fun ERC20::deposit [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+300
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_ERC20_deposit$verify(_$t0: int, _$t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $temp_0'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin': $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $temp_0'address': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+1
    assume {:print "$at(3,2867,2868)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+1
    assume $IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin'($t1);

    // trace_local[_addr]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+1
    assume {:print "$track_local(2,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:77:5+1
    assume {:print "$track_local(2,1,1):", $t1} $t1 == $t1;

    // $t3 := unpack ERC20::Coin($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:79:13+23
    assume {:print "$at(3,2997,3020)"} true;
    $t3 := $value#$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t1);

    // destroy($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:79:27+7

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:84:5+1
    assume {:print "$at(3,3166,3167)"} true;
L1:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:84:5+1
    return;

}

// fun ERC20::initialize_erc20 [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:30:5+581
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_ERC20_initialize_erc20$verify(_$t0: $signer, _$t1: int) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t0: $signer;
    var $t1: int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:30:5+1
    assume {:print "$at(3,706,707)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:30:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<ERC20::Balance>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:30:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'($rsc))));

    // trace_local[module_owner]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:30:5+1
    assume {:print "$track_local(2,2,0):", $t0} $t0 == $t0;

    // trace_local[total_supply]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:30:5+1
    assume {:print "$track_local(2,2,1):", $t1} $t1 == $t1;

    // $t2 := Signer::address_of($t0) on_abort goto L3 with $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:17+33
    assume {:print "$at(3,868,901)"} true;
    call $t2 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(3,868,901)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,2):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t4 := 0x24163afcc6e33b0a9473852e18327fa9 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:54+12
    $t4 := 47967634785951439944328202052269408169;
    assume $IsValid'address'($t4);

    // $t5 := ==($t2, $t4) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:51+2
    $t5 := $IsEqual'address'($t2, $t4);

    // if ($t5) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:9+77
    if ($t5) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:68+17
L1:

    // $t6 := 0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:68+17
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:9+77
    assume {:print "$at(3,860,937)"} true;
    assume {:print "$track_abort(2,2):", $t6} $t6 == $t6;

    // $t3 := move($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:9+77
    $t3 := $t6;

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:32:9+77
    goto L3;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:35:25+13
    assume {:print "$at(3,1033,1046)"} true;
L0:

    // ERC20::publish_balance($t0) on_abort goto L3 with $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:35:9+30
    call $24163afcc6e33b0a9473852e18327fa9_ERC20_publish_balance($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1017,1047)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,2):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t7 := 0x24163afcc6e33b0a9473852e18327fa9 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:37:17+12
    assume {:print "$at(3,1141,1153)"} true;
    $t7 := 47967634785951439944328202052269408169;
    assume $IsValid'address'($t7);

    // $t8 := pack ERC20::Coin($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:37:31+28
    $t8 := $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t1);

    // ERC20::deposit($t7, $t8) on_abort goto L3 with $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:37:9+51
    call $24163afcc6e33b0a9473852e18327fa9_ERC20_deposit($t7, $t8);
    if ($abort_flag) {
        assume {:print "$at(3,1133,1184)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,2):", $t3} $t3 == $t3;
        goto L3;
    }

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:40:5+1
    assume {:print "$at(3,1286,1287)"} true;
L2:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:40:5+1
    return;

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:40:5+1
L3:

    // abort($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:40:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun ERC20::total_supply [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:56:5+115
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_ERC20_total_supply$verify() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply;
    var $t2: int;
    var $t3: int;
    var $temp_0'u64': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume forall $rsc: ResourceDomain<ERC20::TotalSupply>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:56:5+1
    assume {:print "$at(3,1943,1944)"} true;
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply'($rsc))));

    // $t0 := 0x24163afcc6e33b0a9473852e18327fa9 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:57:36+12
    assume {:print "$at(3,2032,2044)"} true;
    $t0 := 47967634785951439944328202052269408169;
    assume $IsValid'address'($t0);

    // $t1 := get_global<ERC20::TotalSupply>($t0) on_abort goto L2 with $t2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:57:9+13
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(3,2005,2018)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<ERC20::TotalSupply>.supply($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:57:9+47
    $t3 := $supply#$24163afcc6e33b0a9473852e18327fa9_ERC20_TotalSupply($t1);

    // trace_return[0]($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:57:9+47
    assume {:print "$track_return(2,4,0):", $t3} $t3 == $t3;

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:58:5+1
    assume {:print "$at(3,2057,2058)"} true;
L1:

    // return $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:58:5+1
    $ret0 := $t3;
    return;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:58:5+1
L2:

    // abort($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:58:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun ERC20::publish_balance [baseline] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:43:5+258
procedure {:inline 1} $24163afcc6e33b0a9473852e18327fa9_ERC20_publish_balance(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t9: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance;
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[account]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:43:5+1
    assume {:print "$at(3,1362,1363)"} true;
    assume {:print "$track_local(2,3,0):", $t0} $t0 == $t0;

    // $t2 := Signer::address_of($t0) on_abort goto L3 with $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:33+27
    assume {:print "$at(3,1478,1505)"} true;
    call $t2 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1478,1505)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t4 := exists<ERC20::Balance>($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:17+6
    $t4 := $ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t2);

    // if ($t4) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    if ($t4) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
L1:

    // destroy($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102

    // $t5 := 2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:89+20
    $t5 := 2;
    assume $IsValid'u64'($t5);

    // $t6 := opaque begin: Errors::already_published($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47

    // assume WellFormed($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47
    assume $IsValid'u64'($t6);

    // assume Eq<u64>($t6, 6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47
    assume $IsEqual'u64'($t6, 6);

    // $t6 := opaque end: Errors::already_published($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47

    // trace_abort($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    assume {:print "$at(3,1454,1556)"} true;
    assume {:print "$track_abort(2,3):", $t6} $t6 == $t6;

    // $t3 := move($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    $t3 := $t6;

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    goto L3;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:46:17+7
    assume {:print "$at(3,1574,1581)"} true;
L0:

    // $t7 := 0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:44:40+1
    assume {:print "$at(3,1441,1442)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack ERC20::Coin($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:44:26+17
    $t8 := $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t7);

    // $t9 := pack ERC20::Balance($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:46:26+29
    assume {:print "$at(3,1583,1612)"} true;
    $t9 := $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance($t8);

    // move_to<ERC20::Balance>($t9, $t0) on_abort goto L3 with $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:46:9+7
    if ($ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $addr#$signer($t0), $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(3,1566,1573)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
    assume {:print "$at(3,1619,1620)"} true;
L2:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
    return;

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
L3:

    // abort($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun ERC20::publish_balance [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:43:5+258
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_ERC20_publish_balance$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t9: $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance;
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:43:5+1
    assume {:print "$at(3,1362,1363)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<ERC20::Balance>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:43:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'($rsc))));

    // trace_local[account]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:43:5+1
    assume {:print "$track_local(2,3,0):", $t0} $t0 == $t0;

    // $t2 := Signer::address_of($t0) on_abort goto L3 with $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:33+27
    assume {:print "$at(3,1478,1505)"} true;
    call $t2 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1478,1505)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t4 := exists<ERC20::Balance>($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:17+6
    $t4 := $ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t2);

    // if ($t4) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    if ($t4) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
L1:

    // destroy($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102

    // $t5 := 2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:89+20
    $t5 := 2;
    assume $IsValid'u64'($t5);

    // $t6 := opaque begin: Errors::already_published($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47

    // assume WellFormed($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47
    assume $IsValid'u64'($t6);

    // assume Eq<u64>($t6, 6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47
    assume $IsEqual'u64'($t6, 6);

    // $t6 := opaque end: Errors::already_published($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:63+47

    // trace_abort($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    assume {:print "$at(3,1454,1556)"} true;
    assume {:print "$track_abort(2,3):", $t6} $t6 == $t6;

    // $t3 := move($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    $t3 := $t6;

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:45:9+102
    goto L3;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:46:17+7
    assume {:print "$at(3,1574,1581)"} true;
L0:

    // $t7 := 0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:44:40+1
    assume {:print "$at(3,1441,1442)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack ERC20::Coin($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:44:26+17
    $t8 := $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t7);

    // $t9 := pack ERC20::Balance($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:46:26+29
    assume {:print "$at(3,1583,1612)"} true;
    $t9 := $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance($t8);

    // move_to<ERC20::Balance>($t9, $t0) on_abort goto L3 with $t3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:46:9+7
    if ($ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $addr#$signer($t0), $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(3,1566,1573)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
    assume {:print "$at(3,1619,1620)"} true;
L2:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
    return;

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
L3:

    // abort($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:47:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun ERC20::transfer [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+185
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_ERC20_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int) returns ()
{
    // declare local variables
    var $t3: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t4: int;
    var $t5: int;
    var $t6: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $temp_0'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin': $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+1
    assume {:print "$at(3,2122,2123)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+1
    assume $IsValid'u64'($t2);

    // assume forall $rsc: ResourceDomain<ERC20::Balance>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'($rsc))));

    // trace_local[from]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+1
    assume {:print "$track_local(2,5,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+1
    assume {:print "$track_local(2,5,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:61:5+1
    assume {:print "$track_local(2,5,2):", $t2} $t2 == $t2;

    // $t4 := Signer::address_of($t0) on_abort goto L2 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:62:30+25
    assume {:print "$at(3,2238,2263)"} true;
    call $t4 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(3,2238,2263)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,5):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := ERC20::withdraw($t4, $t2) on_abort goto L2 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:62:21+43
    call $t6 := $24163afcc6e33b0a9473852e18327fa9_ERC20_withdraw($t4, $t2);
    if ($abort_flag) {
        assume {:print "$at(3,2229,2272)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,5):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[check]($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:62:13+5
    assume {:print "$track_local(2,5,3):", $t6} $t6 == $t6;

    // ERC20::deposit($t1, $t6) on_abort goto L2 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:63:9+18
    assume {:print "$at(3,2282,2300)"} true;
    call $24163afcc6e33b0a9473852e18327fa9_ERC20_deposit($t1, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,2282,2300)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,5):", $t5} $t5 == $t5;
        goto L2;
    }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:64:5+1
    assume {:print "$at(3,2306,2307)"} true;
L1:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:64:5+1
    return;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:64:5+1
L2:

    // abort($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:64:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun ERC20::withdraw [baseline] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+403
procedure {:inline 1} $24163afcc6e33b0a9473852e18327fa9_ERC20_withdraw(_$t0: int, _$t1: int) returns ($ret0: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin)
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance);
    var $t10: $Mutation ($24163afcc6e33b0a9473852e18327fa9_ERC20_Coin);
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t0: int;
    var $t1: int;
    var $temp_0'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin': $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t9));
    assume IsEmptyVec(p#$Mutation($t10));
    assume IsEmptyVec(p#$Mutation($t11));

    // bytecode translation starts here
    // trace_local[addr]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+1
    assume {:print "$at(3,2387,2388)"} true;
    assume {:print "$track_local(2,6,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+1
    assume {:print "$track_local(2,6,1):", $t1} $t1 == $t1;

    // $t4 := ERC20::balance_of($t0) on_abort goto L3 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:68:23+16
    assume {:print "$at(3,2476,2492)"} true;
    call $t4 := $24163afcc6e33b0a9473852e18327fa9_ERC20_balance_of($t0);
    if ($abort_flag) {
        assume {:print "$at(3,2476,2492)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,6):", $t5} $t5 == $t5;
        goto L3;
    }

    // trace_local[balance]($t4) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:68:13+7
    assume {:print "$track_local(2,6,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:25+2
    assume {:print "$at(3,2578,2580)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    if ($t6) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:59+21
L1:

    // $t7 := 1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:59+21
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := opaque begin: Errors::limit_exceeded($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45

    // assume WellFormed($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45
    assume $IsValid'u64'($t8);

    // assume Eq<u64>($t8, 8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45
    assume $IsEqual'u64'($t8, 8);

    // $t8 := opaque end: Errors::limit_exceeded($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45

    // trace_abort($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    assume {:print "$at(3,2562,2635)"} true;
    assume {:print "$track_abort(2,6):", $t8} $t8 == $t8;

    // $t5 := move($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    $t5 := $t8;

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    goto L3;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:59+4
    assume {:print "$at(3,2695,2699)"} true;
L0:

    // $t9 := borrow_global<ERC20::Balance>($t0) on_abort goto L3 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:32+17
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(3,2668,2685)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,6):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t10 := borrow_field<ERC20::Balance>.coin($t9) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:32+37
    $t10 := $ChildMutation($t9, 0, $coin#$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance($Dereference($t9)));

    // $t11 := borrow_field<ERC20::Coin>.value($t10) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:27+48
    $t11 := $ChildMutation($t10, 0, $value#$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($Dereference($t10)));

    // trace_local[balance_ref]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(2,6,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := -($t4, $t1) on_abort goto L3 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:32+1
    assume {:print "$at(3,2744,2745)"} true;
    call $t12 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,2744,2745)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,6):", $t5} $t5 == $t5;
        goto L3;
    }

    // write_ref($t11, $t12) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $t11 := $UpdateMutation($t11, $t12);

    // write_back[Reference($t10).value (u64)]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $t10 := $UpdateMutation($t10, $Update'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin'_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (ERC20::Coin)]($t10) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $t9 := $UpdateMutation($t9, $Update'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'_coin($Dereference($t9), $Dereference($t10)));

    // write_back[ERC20::Balance@]($t9) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := pack ERC20::Coin($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:73:9+22
    assume {:print "$at(3,2762,2784)"} true;
    $t13 := $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t1);

    // trace_return[0]($t13) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:73:9+22
    assume {:print "$track_return(2,6,0):", $t13} $t13 == $t13;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
    assume {:print "$at(3,2789,2790)"} true;
L2:

    // return $t13 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
    $ret0 := $t13;
    return;

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
L3:

    // abort($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun ERC20::withdraw [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+403
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_ERC20_withdraw$verify(_$t0: int, _$t1: int) returns ($ret0: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin)
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance);
    var $t10: $Mutation ($24163afcc6e33b0a9473852e18327fa9_ERC20_Coin);
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $t0: int;
    var $t1: int;
    var $temp_0'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin': $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t9));
    assume IsEmptyVec(p#$Mutation($t10));
    assume IsEmptyVec(p#$Mutation($t11));

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+1
    assume {:print "$at(3,2387,2388)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<ERC20::Balance>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'($rsc))));

    // trace_local[addr]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+1
    assume {:print "$track_local(2,6,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:67:5+1
    assume {:print "$track_local(2,6,1):", $t1} $t1 == $t1;

    // $t4 := ERC20::balance_of($t0) on_abort goto L3 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:68:23+16
    assume {:print "$at(3,2476,2492)"} true;
    call $t4 := $24163afcc6e33b0a9473852e18327fa9_ERC20_balance_of($t0);
    if ($abort_flag) {
        assume {:print "$at(3,2476,2492)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,6):", $t5} $t5 == $t5;
        goto L3;
    }

    // trace_local[balance]($t4) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:68:13+7
    assume {:print "$track_local(2,6,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:25+2
    assume {:print "$at(3,2578,2580)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    if ($t6) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:59+21
L1:

    // $t7 := 1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:59+21
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := opaque begin: Errors::limit_exceeded($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45

    // assume WellFormed($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45
    assume $IsValid'u64'($t8);

    // assume Eq<u64>($t8, 8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45
    assume $IsEqual'u64'($t8, 8);

    // $t8 := opaque end: Errors::limit_exceeded($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:36+45

    // trace_abort($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    assume {:print "$at(3,2562,2635)"} true;
    assume {:print "$track_abort(2,6):", $t8} $t8 == $t8;

    // $t5 := move($t8) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    $t5 := $t8;

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:70:9+73
    goto L3;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:59+4
    assume {:print "$at(3,2695,2699)"} true;
L0:

    // $t9 := borrow_global<ERC20::Balance>($t0) on_abort goto L3 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:32+17
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(3,2668,2685)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,6):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t10 := borrow_field<ERC20::Balance>.coin($t9) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:32+37
    $t10 := $ChildMutation($t9, 0, $coin#$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance($Dereference($t9)));

    // $t11 := borrow_field<ERC20::Coin>.value($t10) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:27+48
    $t11 := $ChildMutation($t10, 0, $value#$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($Dereference($t10)));

    // trace_local[balance_ref]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:71:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(2,6,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := -($t4, $t1) on_abort goto L3 with $t5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:32+1
    assume {:print "$at(3,2744,2745)"} true;
    call $t12 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,2744,2745)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,6):", $t5} $t5 == $t5;
        goto L3;
    }

    // write_ref($t11, $t12) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $t11 := $UpdateMutation($t11, $t12);

    // write_back[Reference($t10).value (u64)]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $t10 := $UpdateMutation($t10, $Update'$24163afcc6e33b0a9473852e18327fa9_ERC20_Coin'_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (ERC20::Coin)]($t10) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $t9 := $UpdateMutation($t9, $Update'$24163afcc6e33b0a9473852e18327fa9_ERC20_Balance'_coin($Dereference($t9), $Dereference($t10)));

    // write_back[ERC20::Balance@]($t9) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:72:9+31
    $24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_ERC20_Balance_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := pack ERC20::Coin($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:73:9+22
    assume {:print "$at(3,2762,2784)"} true;
    $t13 := $24163afcc6e33b0a9473852e18327fa9_ERC20_Coin($t1);

    // trace_return[0]($t13) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:73:9+22
    assume {:print "$track_return(2,6,0):", $t13} $t13 == $t13;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
    assume {:print "$at(3,2789,2790)"} true;
L2:

    // return $t13 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
    $ret0 := $t13;
    return;

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
L3:

    // abort($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/ERC20.move:74:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// struct Message::MessageChangeEvent at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:10:5+115
type {:datatype} $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent;
function {:constructor} $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent($from_message: Vec (int), $to_message: Vec (int)): $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent;
function {:inline} $Update'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'_from_message(s: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent, x: Vec (int)): $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent {
    $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(x, $to_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s))
}
function {:inline} $Update'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'_to_message(s: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent, x: Vec (int)): $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent {
    $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent($from_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s), x)
}
function $IsValid'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(s: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent): bool {
    $IsValid'vec'u8''($from_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s))
      && $IsValid'vec'u8''($to_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s))
}
function {:inline} $IsEqual'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'(s1: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent, s2: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent): bool {
    $IsEqual'vec'u8''($from_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s1), $from_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s2))
    && $IsEqual'vec'u8''($to_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s1), $to_message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent(s2))}

// struct Message::MessageHolder at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:6:5+136
type {:datatype} $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;
function {:constructor} $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($message: Vec (int), $message_change_events: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'): $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;
function {:inline} $Update'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'_message(s: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder, x: Vec (int)): $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder {
    $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(x, $message_change_events#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s))
}
function {:inline} $Update'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'_message_change_events(s: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder, x: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'): $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder {
    $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s), x)
}
function $IsValid'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'(s: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder): bool {
    $IsValid'vec'u8''($message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s))
      && $IsValid'$1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent''($message_change_events#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s))
}
function {:inline} $IsEqual'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'(s1: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder, s2: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder): bool {
    $IsEqual'vec'u8''($message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s1), $message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s2))
    && $IsEqual'$1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent''($message_change_events#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s1), $message_change_events#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder(s2))}
var $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory: $Memory $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;

// fun Message::get_message [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:18:5+215
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_Message_get_message$verify(_$t0: int) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;
    var $t6: Vec (int);
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:18:5+1
    assume {:print "$at(14,423,424)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: ResourceDomain<Message::MessageHolder>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:18:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'($rsc))));

    // trace_local[addr]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:18:5+1
    assume {:print "$track_local(7,0,0):", $t0} $t0 == $t0;

    // $t1 := exists<Message::MessageHolder>($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:17+6
    assume {:print "$at(14,514,520)"} true;
    $t1 := $ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t0);

    // if ($t1) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:9+72
    if ($t1) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:68+11
L1:

    // $t2 := 0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:68+11
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := opaque begin: Errors::not_published($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:46+34

    // assume WellFormed($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:46+34
    assume $IsValid'u64'($t3);

    // assume Eq<u64>($t3, 5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:46+34
    assume $IsEqual'u64'($t3, 5);

    // $t3 := opaque end: Errors::not_published($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:46+34

    // trace_abort($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:9+72
    assume {:print "$at(14,506,578)"} true;
    assume {:print "$track_abort(7,0):", $t3} $t3 == $t3;

    // $t4 := move($t3) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:9+72
    $t4 := $t3;

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:19:9+72
    goto L3;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:20:40+4
    assume {:print "$at(14,619,623)"} true;
L0:

    // $t5 := get_global<Message::MessageHolder>($t0) on_abort goto L3 with $t4 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:20:11+13
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t5 := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(14,590,603)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(7,0):", $t4} $t4 == $t4;
        goto L3;
    }

    // $t6 := get_field<Message::MessageHolder>.message($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:20:10+43
    $t6 := $message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($t5);

    // trace_return[0]($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:20:9+44
    assume {:print "$track_return(7,0,0):", $t6} $t6 == $t6;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:21:5+1
    assume {:print "$at(14,637,638)"} true;
L2:

    // return $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:21:5+1
    $ret0 := $t6;
    return;

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:21:5+1
L3:

    // abort($t4) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:21:5+1
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun Message::set_message [baseline] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+801
procedure {:inline 1} $24163afcc6e33b0a9473852e18327fa9_Message_set_message(_$t0: $signer, _$t1: Vec (int)) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: Vec (int);
    var $t4: $Mutation ($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder);
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent';
    var $t10: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;
    var $t11: $Mutation ($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder);
    var $t12: Vec (int);
    var $t13: $Mutation ($1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent');
    var $t14: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent;
    var $t15: $Mutation (Vec (int));
    var $t0: $signer;
    var $t1: Vec (int);
    var $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder': $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t4));
    assume IsEmptyVec(p#$Mutation($t11));
    assume IsEmptyVec(p#$Mutation($t13));
    assume IsEmptyVec(p#$Mutation($t15));

    // bytecode translation starts here
    // trace_local[account]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+1
    assume {:print "$at(14,644,645)"} true;
    assume {:print "$track_local(7,1,0):", $t0} $t0 == $t0;

    // trace_local[message]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+1
    assume {:print "$track_local(7,1,1):", $t1} $t1 == $t1;

    // $t5 := Signer::address_of($t0) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:25:28+28
    assume {:print "$at(14,769,797)"} true;
    call $t5 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(14,769,797)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // trace_local[account_addr]($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:25:13+12
    assume {:print "$track_local(7,1,2):", $t5} $t5 == $t5;

    // $t7 := exists<Message::MessageHolder>($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:14+6
    assume {:print "$at(14,812,818)"} true;
    $t7 := $ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t5);

    // $t8 := !($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:13+1
    call $t8 := $Not($t7);

    // if ($t8) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    if ($t8) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
L1:

    // goto L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    goto L2;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:27:21+8
    assume {:print "$at(14,871,879)"} true;
L0:

    // $t9 := Event::new_event_handle<Message::MessageChangeEvent>($t0) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:29:40+53
    assume {:print "$at(14,961,1014)"} true;
    call $t9 := $1_Event_new_event_handle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'($t0);
    if ($abort_flag) {
        assume {:print "$at(14,961,1014)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // $t10 := pack Message::MessageHolder($t1, $t9) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:27:31+148
    assume {:print "$at(14,881,1029)"} true;
    $t10 := $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($t1, $t9);

    // move_to<Message::MessageHolder>($t10, $t0) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:27:13+7
    if ($ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $addr#$signer($t0), $t10);
    }
    if ($abort_flag) {
        assume {:print "$at(14,863,870)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    assume {:print "$at(14,807,1439)"} true;
    goto L3;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:32:71+12
    assume {:print "$at(14,1118,1130)"} true;
L2:

    // $t11 := borrow_global<Message::MessageHolder>($t5) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:32:38+17
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t5)) {
        call $ExecFailureAbort();
    } else {
        $t11 := $Mutation($Global($t5), EmptyVec(), $ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t5));
    }
    if ($abort_flag) {
        assume {:print "$at(14,1085,1102)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // trace_local[old_message_holder]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:32:17+18
    $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder' := $Dereference($t11);
    assume {:print "$track_local(7,1,4):", $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'} $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder' == $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder';

    // $t12 := get_field<Message::MessageHolder>.message($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:33:33+27
    assume {:print "$at(14,1165,1192)"} true;
    $t12 := $message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($Dereference($t11));

    // trace_local[from_message]($t12) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:33:17+12
    assume {:print "$track_local(7,1,3):", $t12} $t12 == $t12;

    // $t13 := borrow_field<Message::MessageHolder>.message_change_events($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:34:31+45
    assume {:print "$at(14,1224,1269)"} true;
    $t13 := $ChildMutation($t11, 1, $message_change_events#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($Dereference($t11)));

    // $t14 := pack Message::MessageChangeEvent($t12, $t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:34:78+106
    $t14 := $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent($t12, $t1);

    // Event::emit_event<Message::MessageChangeEvent>($t13, $t14) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:34:13+172
    call $t13 := $1_Event_emit_event'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'($t13, $t14);
    if ($abort_flag) {
        assume {:print "$at(14,1206,1378)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // $t15 := borrow_field<Message::MessageHolder>.message($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+26
    assume {:print "$at(14,1392,1418)"} true;
    $t15 := $ChildMutation($t11, 0, $message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($Dereference($t11)));

    // write_ref($t15, $t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+36
    $t15 := $UpdateMutation($t15, $t1);

    // write_back[Reference($t11).message (vector<u8>)]($t15) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+36
    $t11 := $UpdateMutation($t11, $Update'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'_message($Dereference($t11), $Dereference($t15)));

    // write_back[Message::MessageHolder@]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+36
    $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $GlobalLocationAddress($t11),
        $Dereference($t11));

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    assume {:print "$at(14,807,1439)"} true;
L3:

    // label L4 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
    assume {:print "$at(14,1444,1445)"} true;
L4:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
    return;

    // label L5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
L5:

    // abort($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun Message::set_message [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+801
procedure {:timeLimit 40} $24163afcc6e33b0a9473852e18327fa9_Message_set_message$verify(_$t0: $signer, _$t1: Vec (int)) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: Vec (int);
    var $t4: $Mutation ($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder);
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: $1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent';
    var $t10: $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;
    var $t11: $Mutation ($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder);
    var $t12: Vec (int);
    var $t13: $Mutation ($1_Event_EventHandle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent');
    var $t14: $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent;
    var $t15: $Mutation (Vec (int));
    var $t0: $signer;
    var $t1: Vec (int);
    var $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder': $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t4));
    assume IsEmptyVec(p#$Mutation($t11));
    assume IsEmptyVec(p#$Mutation($t13));
    assume IsEmptyVec(p#$Mutation($t15));

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+1
    assume {:print "$at(14,644,645)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+1
    assume $IsValid'vec'u8''($t1);

    // assume forall $rsc: ResourceDomain<Message::MessageHolder>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'($rsc))));

    // trace_local[account]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+1
    assume {:print "$track_local(7,1,0):", $t0} $t0 == $t0;

    // trace_local[message]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:23:5+1
    assume {:print "$track_local(7,1,1):", $t1} $t1 == $t1;

    // $t5 := Signer::address_of($t0) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:25:28+28
    assume {:print "$at(14,769,797)"} true;
    call $t5 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(14,769,797)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // trace_local[account_addr]($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:25:13+12
    assume {:print "$track_local(7,1,2):", $t5} $t5 == $t5;

    // $t7 := exists<Message::MessageHolder>($t5) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:14+6
    assume {:print "$at(14,812,818)"} true;
    $t7 := $ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t5);

    // $t8 := !($t7) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:13+1
    call $t8 := $Not($t7);

    // if ($t8) goto L0 else goto L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    if ($t8) { goto L0; } else { goto L1; }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
L1:

    // goto L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    goto L2;

    // label L0 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:27:21+8
    assume {:print "$at(14,871,879)"} true;
L0:

    // $t9 := Event::new_event_handle<Message::MessageChangeEvent>($t0) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:29:40+53
    assume {:print "$at(14,961,1014)"} true;
    call $t9 := $1_Event_new_event_handle'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'($t0);
    if ($abort_flag) {
        assume {:print "$at(14,961,1014)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // $t10 := pack Message::MessageHolder($t1, $t9) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:27:31+148
    assume {:print "$at(14,881,1029)"} true;
    $t10 := $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($t1, $t9);

    // move_to<Message::MessageHolder>($t10, $t0) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:27:13+7
    if ($ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $addr#$signer($t0), $t10);
    }
    if ($abort_flag) {
        assume {:print "$at(14,863,870)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // goto L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    assume {:print "$at(14,807,1439)"} true;
    goto L3;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:32:71+12
    assume {:print "$at(14,1118,1130)"} true;
L2:

    // $t11 := borrow_global<Message::MessageHolder>($t5) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:32:38+17
    if (!$ResourceExists($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t5)) {
        call $ExecFailureAbort();
    } else {
        $t11 := $Mutation($Global($t5), EmptyVec(), $ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $t5));
    }
    if ($abort_flag) {
        assume {:print "$at(14,1085,1102)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // trace_local[old_message_holder]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:32:17+18
    $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder' := $Dereference($t11);
    assume {:print "$track_local(7,1,4):", $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'} $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder' == $temp_0'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder';

    // $t12 := get_field<Message::MessageHolder>.message($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:33:33+27
    assume {:print "$at(14,1165,1192)"} true;
    $t12 := $message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($Dereference($t11));

    // trace_local[from_message]($t12) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:33:17+12
    assume {:print "$track_local(7,1,3):", $t12} $t12 == $t12;

    // $t13 := borrow_field<Message::MessageHolder>.message_change_events($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:34:31+45
    assume {:print "$at(14,1224,1269)"} true;
    $t13 := $ChildMutation($t11, 1, $message_change_events#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($Dereference($t11)));

    // $t14 := pack Message::MessageChangeEvent($t12, $t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:34:78+106
    $t14 := $24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent($t12, $t1);

    // Event::emit_event<Message::MessageChangeEvent>($t13, $t14) on_abort goto L5 with $t6 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:34:13+172
    call $t13 := $1_Event_emit_event'$24163afcc6e33b0a9473852e18327fa9_Message_MessageChangeEvent'($t13, $t14);
    if ($abort_flag) {
        assume {:print "$at(14,1206,1378)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(7,1):", $t6} $t6 == $t6;
        goto L5;
    }

    // $t15 := borrow_field<Message::MessageHolder>.message($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+26
    assume {:print "$at(14,1392,1418)"} true;
    $t15 := $ChildMutation($t11, 0, $message#$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder($Dereference($t11)));

    // write_ref($t15, $t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+36
    $t15 := $UpdateMutation($t15, $t1);

    // write_back[Reference($t11).message (vector<u8>)]($t15) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+36
    $t11 := $UpdateMutation($t11, $Update'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'_message($Dereference($t11), $Dereference($t15)));

    // write_back[Message::MessageHolder@]($t11) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:38:13+36
    $24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory := $ResourceUpdate($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $GlobalLocationAddress($t11),
        $Dereference($t11));

    // label L3 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:26:9+632
    assume {:print "$at(14,807,1439)"} true;
L3:

    // label L4 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
    assume {:print "$at(14,1444,1445)"} true;
L4:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
    return;

    // label L5 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
L5:

    // abort($t6) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/Message.move:40:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun set_message::set_message [verification] at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:4:5+109
procedure {:timeLimit 40} $ffffffffffffffffffffffffffffffff_set_message_set_message$verify(_$t0: $signer, _$t1: Vec (int)) returns ()
{
    // declare local variables
    var $t2: int;
    var $t0: $signer;
    var $t1: Vec (int);
    var $temp_0'signer': $signer;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:4:5+1
    assume {:print "$at(7,39,40)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:4:5+1
    assume $IsValid'vec'u8''($t1);

    // assume forall $rsc: ResourceDomain<Message::MessageHolder>(): WellFormed($rsc) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:4:5+1
    assume (forall $a_0: int :: {$ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $a_0)}(var $rsc := $ResourceValue($24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder_$memory, $a_0);
    ($IsValid'$24163afcc6e33b0a9473852e18327fa9_Message_MessageHolder'($rsc))));

    // trace_local[account]($t0) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:4:5+1
    assume {:print "$track_local(8,0,0):", $t0} $t0 == $t0;

    // trace_local[message]($t1) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:4:5+1
    assume {:print "$track_local(8,0,1):", $t1} $t1 == $t1;

    // Message::set_message($t0, $t1) on_abort goto L2 with $t2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:5:9+38
    assume {:print "$at(7,103,141)"} true;
    call $24163afcc6e33b0a9473852e18327fa9_Message_set_message($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(7,103,141)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(8,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:6:5+1
    assume {:print "$at(7,147,148)"} true;
L1:

    // return () at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:6:5+1
    return;

    // label L2 at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:6:5+1
L2:

    // abort($t2) at /Users/emmazjy/repos/move-hackathon-tutorial/step_4/main/sources/set_message.move:6:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}
