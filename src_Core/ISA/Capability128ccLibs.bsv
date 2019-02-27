/*
 * Copyright (c) 2015 Jonathan Woodruff
 * Copyright (c) 2017 Alexandre Joannou
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-10-C-0237
 * ("CTSRD"), as part of the DARPA CRASH research programme.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

//import Debug::*;
import DefaultValue::*;
import MIPS::*;
//import VnD::*;
//import Assert::*;

typedef struct {
    Bool v;
    ty   d;
} VnD #(type ty) deriving (Eq, Bits);

`ifdef CAP64
    typedef 0  UPermW;
    typedef 10 MW;
    typedef 6  ExpW;
    typedef 6  OTypeW;
    typedef 32 CapAddressW;
    typedef 64 CapW;
`else // CAP128 is default
    typedef 4   UPermW;
    typedef 14  MW;
    typedef 6   ExpW;
    typedef 18  OTypeW;
    typedef 64  CapAddressW;
    typedef 128 CapW;
`endif
typedef TDiv#(ExpW,2)      HalfExpW;
typedef TSub#(MW,HalfExpW) UpperMW;

// The compressed bounds field type
typedef TSub#(TMul#(MW,2),1) CBoundsW;
typedef Bit#(CBoundsW) CBounds;
// The pointer CapAddress type
typedef Bit#(CapAddressW) CapAddress;
// The Hardware permissions type
typedef struct {
    Bool reserved;
    Bool acces_sys_regs;
    Bool permit_unseal;
    Bool permit_ccall;
    Bool permit_seal;
    Bool permit_store_ephemeral_cap;
    Bool permit_store_cap;
    Bool permit_load_cap;
    Bool permit_store;
    Bool permit_load;
    Bool permit_execute;
    Bool non_ephemeral;
} HPerms deriving(Bits, Eq, FShow); // 12 bits
// The permissions field, including both "soft" and "hard" permission bits.
typedef struct {
    Bit#(UPermW)  soft;
    HPerms     hard;
} Perms deriving(Bits, Eq, FShow);
typedef SizeOf#(Perms) PermsW;
// The reserved bits
typedef TSub#(CapW,TAdd#(CapAddressW,TAdd#(OTypeW,TAdd#(CBoundsW,PermsW)))) ResW;
// The full capability structure, including the "tag" bit.
typedef struct {
  Bool          isCapability;
  Perms         perms;
  Bit#(ResW)    reserved;
  Bit#(OTypeW)  otype;
  CBounds       bounds;
  CapAddress    address;
} CapabilityInMemory deriving(Bits, Eq, FShow); // CapW + 1 (tag bit)
// The full capability structure as Bits, including the "tag" bit.
typedef Bit#(TAdd#(CapW,1)) Capability;
// not including the tag bit
typedef Bit#(CapW) CapBits;
typedef Bit#(128) ShortCap;
/* TODO
staticAssert(valueOf(SizeOf#(CapabilityInMemory))==valueOf(SizeOf#(Capability)),
    "The CapabilityInMemory type has incorrect size of " + integerToString(valueOf(SizeOf#(CapabilityInMemory))) + " (CapW = " + integerToString(valueOf(CapW)) + ")"
);
*/
// Bit type of the debug capability
//typedef Bit#(CapW) DebugCap;
// large capability address type (with extra bits at the top)
typedef Bit#(TAdd#(CapAddressW,2)) LCapAddress;
// Format of the cheri concentrate capability
typedef enum {Exp0, EmbeddedExp} Format deriving (Bits, Eq, FShow);
// Exponent type
typedef UInt#(ExpW) Exp;
// Type for capability otype field
typedef VnD#(Bit#(OTypeW)) CType;
// unpacked capability format
typedef struct {
  Bool          isCapability;
  LCapAddress   address;
  Bit#(MW)      addrBits;
  Perms         perms;
  Bit#(ResW)    reserved;
  Bit#(OTypeW)  otype;
  Format        format;
  Bounds        bounds;
} CapFat deriving(Bits, Eq);

// "Architectural FShow"
function Fmt showArchitectural(CapFat cap) =
    $format("valid:%b", cap.isCapability)
    + $format(" perms:0x%x", getPerms(cap))
    + $format(" sealed:%b", isSealed(cap))
    + $format(" type:0x%x",getType(cap))
    + $format(" offset:0x%x", getOffsetFat(cap, getTempFields(cap)))
    + $format(" base:0x%x", getBotFat(cap, getTempFields(cap)))
    + $format(" length:0x%x", getLengthFat(cap, getTempFields(cap)));

// "Microarchitectural FShow"
instance FShow#(CapFat);
    function Fmt fshow(CapFat cap) =
        $format("valid:%b", cap.isCapability)
        + $format(" perms:0x%x", getPerms(cap))
        + $format(" reserved:0x%x", cap.reserved)
        + $format(" format:", fshow(cap.format))
        + $format(" bounds:", fshow(cap.bounds))
        + $format(" address:0x%x", cap.address)
        + $format(" addrBits:0x%x", cap.addrBits)
        + $format(" {bot:0x%x top:0x%x len:0x%x offset:0x%x}",
                    getBotFat(cap, getTempFields(cap)),
                    getTopFat(cap, getTempFields(cap)),
                    getLengthFat(cap, getTempFields(cap)),
                    getOffsetFat(cap, getTempFields(cap)))
        + $format(" (TempFields: {") + fshow(getTempFields(cap)) + $format("})");
endinstance

// default value for CatFat
CapFat defaultCapFat = defaultValue;

// Capability register index type
typedef Bit#(6) CapReg;

// unpack a memory representation of the capability
function CapFat unpackCap(Capability thin);
    CapabilityInMemory memCap = unpack(thin);
    // extract the fields from the memory capability
    CapFat fat = defaultValue;
    fat.isCapability = memCap.isCapability;
    fat.perms        = memCap.perms;
    fat.reserved     = memCap.reserved;
    fat.otype        = memCap.otype;
    match {.f, .b}   = decBounds(memCap.bounds);
    fat.format       = f;
    fat.bounds       = b;
    fat.address      = zeroExtend(memCap.address);
    // The next few lines are to optimise the critical path of generating addrBits.
    // The value of Exp can now be 0 or come from token, so assume they come from the token,
    // then select the lower bits at the end if they didn't after all.
    BoundsEmbeddedExp tmp = unpack(memCap.bounds);
    Exp potentialExp = unpack({tmp.expTopHalf,tmp.expBotHalf});
    Bit#(MW) potentialAddrBits = truncate(memCap.address >> potentialExp);
    fat.addrBits = (tmp.embeddedExp)?potentialAddrBits:truncate(memCap.address);
    return fat;
endfunction

// pack the fat capability into the memory representation
function Capability packCap(CapFat fat);
  CapabilityInMemory thin = CapabilityInMemory{
      isCapability: fat.isCapability,
      perms: fat.perms,
      reserved: fat.reserved,
      otype: fat.otype,
      bounds: encBounds(fat.format,fat.bounds),
      address: truncate(fat.address)
  };
  return pack(thin);
endfunction

// XXX needs double checking
function ShortCap getShortCap (CapFat cap);
    CapabilityInMemory ret = unpack(packCap(cap));
    // put tag bit in highest reserved bit
    ret.reserved[valueOf(ResW)-1] = pack(cap.isCapability);
    CapBits retbits = truncate(pack(ret));
    return zeroExtend(retbits);
endfunction

// The temporary fields
typedef MetaInfo TempFields;

// Is the capability format imprecise
Bool imprecise = True;

// Interface functions
//------------------------------------------------------------------------------
function LCapAddress getBotFat(CapFat cap, TempFields tf);
    // First, construct a full length value with the base bits and the
    // correction bits above, and shift that value to the appropriate spot.
    LCapAddress addBase = signExtend({pack(tf.baseCorrection), cap.bounds.baseBits}) << cap.bounds.exp;
    // Build a mask on the high bits of a full length value to extract the high
    // bits of the address.
    Bit#(TSub#(SizeOf#(LCapAddress),MW)) mask = ~0 << cap.bounds.exp;
    // Extract the high bits of the address (and append the implied zeros at the
    // bottom), and add with the previously prepared value.
    return {truncateLSB(cap.address)&mask,0} + addBase;
endfunction
function LCapAddress getTopFat(CapFat cap, TempFields tf);
    // First, construct a full length value with the top bits and the
    // correction bits above, and shift that value to the appropriate spot.
    LCapAddress addTop = signExtend({pack(tf.topCorrection), cap.bounds.topBits}) << cap.bounds.exp;
    // Build a mask on the high bits of a full length value to extract the high
    // bits of the address.
    Bit#(TSub#(SizeOf#(LCapAddress),MW)) mask = ~0 << cap.bounds.exp;
    // Extract the high bits of the address (and append the implied zeros at the
    // bottom), and add with the previously prepared value.
    return {truncateLSB(cap.address)&mask,0} + addTop;
endfunction
function LCapAddress getLengthFat(CapFat cap, TempFields tf);
    // Get the top and base bits with the 2 correction bits prepended
    Bit#(TAdd#(MW,2)) top  = {pack(tf.topCorrection),cap.bounds.topBits};
    Bit#(TAdd#(MW,2)) base = {pack(tf.baseCorrection),cap.bounds.baseBits};
    // Get the length by substracting base from top and shifting appropriately
    LCapAddress length = zeroExtend(top - base) << cap.bounds.exp;
    // Return a saturated length in case of big exponent
    return (cap.bounds.exp >= resetExp) ? ~0 : length;
endfunction
function Address getOffsetFat(CapFat cap, TempFields tf);
    // Get the exponent
    Exp e = cap.bounds.exp;
    // Get the base bits with the 2 correction bits prepended
    Bit#(TAdd#(MW,2)) base = {pack(tf.baseCorrection),cap.bounds.baseBits};
    // Get the offset bits by substracting the previous value from the addrBits
    Bit#(TAdd#(MW,2)) offset = zeroExtend(cap.addrBits) - base;
    // Grab the bottom bits of the address
    Address addrLSB = lAddrToReg(cap.address & ~(~0 << e));
    // Return the computed offset bits (sign extended) shifted appropriatly,
    // with the low address bits appended
    return (signExtend(offset) << e) | addrLSB;
endfunction
function LCapAddress getAddress(CapFat cap) = cap.address;
function Address lAddrToReg(LCapAddress in);
    CapAddress retVal = truncate(in);
    return signExtend(retVal);
endfunction
function LCapAddress regToLAddr(Address in);
    CapAddress retVal = truncate(in);
    return zeroExtend(retVal);
endfunction
function LCapAddress regToSignedLAddr(Address in);
    CapAddress retVal = truncate(in);
    return signExtend(retVal);
endfunction
function Bool isSealed(CapFat cap) = cap.otype != -1;
function CType getType(CapFat cap) = VnD{v: (cap.otype != -1), d: cap.otype};
function Bit#(64) getPerms(CapFat cap);
    Bit#(15) hardPerms = zeroExtend(pack(cap.perms.hard));
    Bit#(16) softPerms = zeroExtend(pack(cap.perms.soft));
    return zeroExtend({softPerms,hardPerms});
endfunction
function TempFields getTempFields(CapFat cap) = getMetaInfo(cap);
function Bool privileged(CapFat cap) = cap.perms.hard.acces_sys_regs;
function CapExpCode checkRegAccess(CapFat cap, CapReg cr, Privilege priv);
  CapExpCode ret = None;
  // Permissions for protected registers accessed by CReadHwr and CWriteHwr
  if (!cap.perms.hard.acces_sys_regs && (cr>=32+8 && cr<32+16))
    ret = SysRegs;
  if (priv!=Kernel && (cr>=32+16 && cr<32+24))
    ret = SysRegs;
  if ((!cap.perms.hard.acces_sys_regs || priv!=Kernel) && (cr>=32+24 && cr<=32+31))
    ret = SysRegs;
  return ret;
endfunction
function Bool capInBounds(CapFat cap, TempFields tf, Bool inclusive);
    // Check that the pointer of a capability is currently within the bounds
    // of the capability
    Bool ptrVStop = (inclusive) ? (cap.addrBits<=cap.bounds.topBits) : (cap.addrBits<cap.bounds.topBits);
    // Top is ok if the pointer and top are in the same alignment region
    // and the pointer is less than the top.  If they are not in the same
    // alignment region, it's ok if the top is in Hi and the bottom in Low.
    Bool topOk  = (tf.topHi == tf.addrHi)  ? (ptrVStop) : tf.topHi;
    Bool baseOk = (tf.baseHi == tf.addrHi) ? (cap.addrBits >= cap.bounds.baseBits) : tf.addrHi;
    return topOk && baseOk;
endfunction
function CapFat nullifyCap(CapFat cap);
    CapFat ret      = nullCap;
    CapAddress tmpAddr = truncate(cap.address);
    ret.addrBits    = {2'b0,truncateLSB(tmpAddr)};
    ret.address     = cap.address;
    return ret;
endfunction
function CapFat pccJumpUpdate(CapFat pcc, LCapAddress fullBot);
    // Set the appropriate fields in PCC when jumping.
    pcc.address  = fullBot;
    pcc.addrBits = pcc.bounds.baseBits;
    return pcc;
endfunction
function CapFat setCapPointer(CapFat cap, CapAddress pointer);
    // Function to "cheat" and just set the pointer when we know that
    // it will be in representable bounds by some other means.
    CapFat ret   = cap;
    ret.address  = zeroExtend(pointer);
    ret.addrBits = truncate(ret.address >> ret.bounds.exp);
    return ret;
endfunction
// Only currently used for algorithm comparison.

function ActionValue#(Bool) boundsCheck(CapFat cap, Bit#(64) off, TempFields tf);
  actionvalue
    Bit#(66) bo = zeroExtend(off);
    cap <- incOffset(cap, cap.address+truncate(bo), off, tf, False);
    return cap.isCapability && capInBounds(cap, tf, False);
  endactionvalue
endfunction

function Bit#(n) smearMSBRight(Bit#(n) x);
    Bit#(n) res = x;
    for (Integer i = 0; i < valueOf(TLog#(n))-1; i = i + 1)
        res = res | (res >> 2**i);
    return res;
endfunction

function ActionValue#(CapFat) setBounds(CapFat cap, Address lengthFull, Bool exact) =
    actionvalue
        //debug2("cap", $display("SETBOUNDS --- initial cap ", fshow(cap)));
        //debug2("cap", $display("SETBOUNDS --- length 0x%x", lengthFull));
        //debug2("cap", $display("SETBOUNDS --- is exact 0b%b", exact));
        CapFat ret = cap;
        // Find new exponent by finding the index of the most significant bit of the
        // length, or counting leading zeros in the high bits of the length, and
        // substracting them to the CapAddress width (taking away the bottom MW-1 bits:
        // trim (MW-1) bits from the bottom of length since any length with a significance
        // that small will yield an exponent of zero).
        CapAddress length = truncate(lengthFull);
        Bit#(TSub#(CapAddressW,TSub#(MW,1))) lengthMSBs = truncateLSB(length);
        Exp zeros = zeroExtend(countZerosMSB(lengthMSBs));
        // Adjust resetExp by one since it's scale reaches 1-bit greater than a 64-bit length
        // can express.
        Bool maxZero = (zeros==(resetExp-1));
        // Do this without subtraction
        //fromInteger(valueof(TSub#(SizeOf#(Address),TSub#(MW,1)))) - zeros;
        Exp e = (resetExp-1) - zeros;
        //debug2("cap", $display("SETBOUNDS --- zeros=%d, new exp %d", zeros, e));
        // Force otype to unsealed.
        ret.otype = -1;
        // Derive new base bits by extracting MW bits from the capability
        // address starting at the new exponent's position.
        CapAddress tmpAddr = truncate(cap.address);
        LCapAddress base = zeroExtend(tmpAddr);
        Bit#(TAdd#(MW,1)) newBaseBits = truncate(base>>e);
        
        //debug2("cap", $display("SETBOUNDS --- newBaseBits 0x%x", newBaseBits));
        // Derive new top bits by extracting MW bits from the capability
        // address + requested length, starting at the new exponent's position,
        // and rounding up if significant bits are lost in the process.
        LCapAddress len = zeroExtend(length);
        LCapAddress top = base + len;
        Bit#(TAdd#(MW,1)) newTopBits = truncate(top>>e);
        // The shift amount required to put the most significant set bit of the
        // len just above the bottom HalfExpW bits that are taken by the exp.
        Integer shiftAmount = valueOf(TSub#(TSub#(MW,2),HalfExpW));
        // Round up considering the stolen HalfExpW exponent bits if required
        Exp lenRoundShift = fromInteger(shiftAmount);
        LCapAddress roundedLength = len+(len>>lenRoundShift);
        Integer bitsUsedByExp = valueOf(HalfExpW);
        Bit#(UpperMW) newTopBitsRounded = truncate(((base+roundedLength)>>e)>>bitsUsedByExp);
        // This value is just to avoid adding later.
        lenRoundShift = fromInteger(shiftAmount-2);
        roundedLength = len+(len>>lenRoundShift);
        Bit#(UpperMW) newTopBitsRoundedHigher = truncate(((base+roundedLength)>>e)>>(1+bitsUsedByExp));
        //debug2("cap", $display("SETBOUNDS --- newTopBits 0x%x", newTopBits));
        // Check if non-zero bits were lost in the low bits of top, either in the 'e'
        // shifted out bits or in the HalfExpW bits stolen for the exponent by creating
        // a mask with all bits set below the MSB of length and then masking all bits
        // below the mantissa bits.
        LCapAddress lmask = smearMSBRight(len);
        // Shift by MW-1 to move MSB of mask just below the mantissa, then up HalfExpW
        // more to take in the bits that will be lost for the exponent when it is non-zero.
        LCapAddress lmaskLo = lmask>>fromInteger(shiftAmount+1);
        Bool lostSignificantTop  = (top&lmaskLo)!=0 && !maxZero;
        //debug2("cap", $display("SETBOUNDS --- lostSignificantTop %b", lostSignificantTop));
        // Check if non-zero bits were lost in the low bits of base, either in the 'e'
        // shifted out bits or in the HalfExpW bits stolen for the exponent
        Bool lostSignificantBase = (base&lmaskLo)!=0 && !maxZero;
        //debug2("cap", $display("SETBOUNDS --- lostSignificantBase %b", lostSignificantBase));
        // If either base or top lost significant bits and we wanted an exact setBounds,
        // void the return capability
        if (exact && (lostSignificantBase || lostSignificantTop)) ret.isCapability = False;
        //debug2("cap", $display("SETBOUNDS --- is return voided %b", !ret.isCapability));
        // We need to round up Exp if we round either bound and if the length is at the maximum.
        // The MSB of the length corrosponding to the length will be at MW-1 for it to be implied
        // correctly, but if we round either bound out, we will increase by 1 and this may push
        // the MSB up by one.
        // The lomask for checking for potential overflow should mask one more bit of the mantissa.
        lmaskLo = lmask>>fromInteger(shiftAmount-1);
        //debug2("cap", $display("SETBOUNDS --- lengthMax check, length: %x, lmask: %x, lmaskLo: %x, masked: %x", len, lmask, lmaskLo, (len&(~lmaskLo))));
        Bool lengthMax = (len&(~lmaskLo))==(lmask&(~lmaskLo));
        if(lengthMax && !maxZero) begin
           e = e+1;
           ret.bounds.topBits = {newTopBitsRoundedHigher,0};
           ret.bounds.baseBits = truncateLSB(newBaseBits);
        end else if (lostSignificantTop) begin
          ret.bounds.topBits = {newTopBitsRounded,0};
          //debug2("cap", $display("SETBOUNDS --- topbits after rounding %x", ret.bounds.topBits));
          ret.bounds.baseBits = truncate(newBaseBits);
        end else begin
          ret.bounds.topBits = truncate(newTopBits);
          //debug2("cap", $display("SETBOUNDS --- topbits after rounding %x", ret.bounds.topBits));
          ret.bounds.baseBits = truncate(newBaseBits);
        end
        
        ret.bounds.exp = e;
        // Update the addrBits fields
        ret.addrBits = ret.bounds.baseBits;
        // Derive new format from newly computed exponent value, and round top up if
        // necessary
        if (maxZero) begin
            ret.format = Exp0;
        end else begin
            ret.format = EmbeddedExp;
            Bit#(HalfExpW) botZeroes = 0;
            ret.bounds.baseBits = {truncateLSB(ret.bounds.baseBits), botZeroes};
            ret.bounds.topBits  = {truncateLSB(ret.bounds.topBits), botZeroes};
        end
        
        // Return derived capability
        //debug2("cap", $display("SETBOUNDS --- returning ", fshow(ret)));
        return ret;
    endactionvalue;
function ActionValue#(CapFat) seal(CapFat cap, TempFields tf, CType otype) =
    actionvalue
        CapFat ret = cap;
        // Update the fields of the new sealed capability (otype)
        ret.otype = otype.d;
        return ret;
    endactionvalue;
function ActionValue#(CapFat) unseal(CapFat cap, x _) =
    actionvalue
        CapFat ret = cap;
        ret.otype = -1;
        return ret;
    endactionvalue;
function ActionValue#(CapFat) incOffset(CapFat cap, LCapAddress pointer, Bit#(64) offset/*this is the increment in inc offset, and the offset in set offset*/, TempFields tf, Bool setOffset) =
// NOTE:
// The 'offset' argument is the "increment" value when setOffset is false,
// and the actual "offset" value when setOffset is true.
//
// For this function to work correctly, we must have 'offset' = 'pointer'-'cap.address'.
// In the most critical case we have both available and picking one or the other
// is less efficient than passing both.  If the 'setOffset' flag is set, this function will
// ignore the 'pointer' argument and use 'offset' to set the offset of 'cap' by adding it to
// the capability base. If the 'setOffset' flag is not set, this function will increment the
// offset of 'cap' by replacing the 'cap.address' field with the 'pointer' argument (with
// the assumption that the 'pointer' argument is indeed equal to 'cap.address'+'offset'.
// The 'cap.addrBits' field is also updated accordingly.
    actionvalue
        CapFat ret = cap;
        Exp e = cap.bounds.exp;
        // Updating the address of a capability requires checking that the new address
        // is still within representable bounds. For capabilities with big representable
        // regions (with exponents >= resetExp), there is no representability issue.
        // For the other capabilities, the check consists of two steps:
        // - A "inRange" test
        // - A "inLimits" test

        // The inRange test
        // ----------------
        // Conceptually, the inRange test checks the magnitude of 'offset' is less then
        // the representable region’s size S. This ensures that the inLimits test result
        // is meaningful. The test succeeds if the absolute value of 'offset' is less than S,
        // that is −S < 'offset' < S. This test reduces to a check that there are no
        // significant bits in the high bits of 'offset', that is they are all ones or all
        // zeros. This is tested for by comparing the high bits of 'offset' with those same
        // bits rotated by one (if these are the same, all bits are the same, there are no
        // significant bits).
        CapAddress offsetAddr = truncate(offset);
        Bit#(TSub#(CapAddressW,MW)) signBits       = signExtend(offset[63]);
        Bit#(TSub#(CapAddressW,MW)) highOffsetBits = unpack(truncateLSB(offsetAddr));
        Bit#(TSub#(CapAddressW,MW)) highBitsfilter = -1 << e;
        highOffsetBits = (highOffsetBits ^ signBits) & highBitsfilter;
        Bool inRange = (highOffsetBits == 0);

        // The inLimits test
        // -----------------
        // Conceptually, the inLimits test ensures that neither the of the edges of the
        // representable region have been crossed with the new address. In essence, it
        // compares the distance 'offsetBits' added (on MW bits) with the distance 'toBounds'
        // to the edge of the representable space (on MW bits).
        // - For a positive or null increment
        //   inLimits = offsetBits < toBounds - 1
        // - For a negative increment:
        //   inLimits = (offsetBits >= toBounds) and ('we were not already on the bottom edge')
        //   (when already on the bottom edge of the representable space, the relevant
        //   bits of the address and those of the representable edge are the same, leading
        //   to a false positive on the i >= toBounds comparison)

        // The sign of the increment
        Bool posInc = offsetAddr[valueOf(CapAddressW)-1] == 1'b0;

        // The offsetBits value corresponds to the appropriate slice of the 'offsetAddr' argument
        Bit#(MW) offsetBits  = truncate(offsetAddr >> e);

        // The toBounds value is given by substracting the address of the capability from the
        // address of the edge of the representable region (on MW bits) when the 'setOffset'
        // flag is not set. When it is set, it is given by substracting the base address of
        // the capability from the edge of the representable region (on MW bits).
        // This value is both the distance to the representable top and the distance to the
        // representable bottom (when appended to a one for negative sign), a convenience of
        // the two's complement representation.

        // NOTE: When the setOffset flag is set, toBounds should be the distance from the base
        // to the representable edge. This can be computed efficiently, and without relying on
        // the temporary fields, as follows:
        // equivalent to (repBoundBits - cap.bounds.baseBits):
        Bit#(MW) toBounds_A   = {3'b111,0} - {3'b000,truncate(cap.bounds.baseBits)};
        // equivalent to (repBoundBits - cap.bounds.baseBits - 1):
        Bit#(MW) toBoundsM1_A = {3'b110,~truncate(cap.bounds.baseBits)};
        /*
        XXX not sure if we still care about that
        if (toBoundsM1_A != (toBounds_A-1)) $display("error %x", toBounds_A[15:13]);
        */
        // When the setOffset flag is not set, we need to use the temporary fields with the
        // upper bits of the representable bounds
        Bit#(MW) repBoundBits = {tf.repBoundTopBits,0};
        Bit#(MW) toBounds_B   = repBoundBits - cap.addrBits;
        Bit#(MW) toBoundsM1_B = repBoundBits + ~cap.addrBits;
        // Select the appropriate toBounds value
        Bit#(MW) toBounds   = (setOffset) ? toBounds_A   : toBounds_B;
        Bit#(MW) toBoundsM1 = (setOffset) ? toBoundsM1_A : toBoundsM1_B;

        // Implement the inLimit test
        Bool inLimits = False;
        if (posInc) begin
            // For a positive or null increment
            inLimits = offsetBits < toBoundsM1;
        end else begin
            // For a negative increment
            inLimits = (offsetBits >= toBounds) && (repBoundBits != cap.addrBits);
        end

        // Complete representable bounds check
        // -----------------------------------
        Bool inBounds = (inRange && inLimits) || (e >= resetExp);

        // Updating the return capability
        // ------------------------------
        if (setOffset) begin
            // Get the base and add the offsetAddr. This could be slow, but seems to pass timing.
            ret.address = getBotFat(cap,tf) + zeroExtend(offsetAddr);
            // TODO write comments on this
            Bit#(TAdd#(MW,2)) newAddrBits = zeroExtend(cap.bounds.baseBits) + zeroExtend(offsetBits);
            ret.addrBits = (e == resetExp) ? {1'b0,truncate(newAddrBits)}:truncate(newAddrBits);
        end else begin
            // In the incOffset case, the 'pointer' argument already contains the new address
            CapAddress tmpAddr = truncate(pointer);
            ret.address  = zeroExtend(tmpAddr);
            ret.addrBits = truncate(pointer >> e);
        end
        // Nullify the capability if the representable bounds check has failed
        if (!inBounds) ret = nullifyCap(ret);

        // return updated / invalid capability
        return ret;
    endactionvalue;

///////////////////////////////
// Internal types and values //
////////////////////////////////////////////////////////////////////////////////


// Exponent that pushes the implied +1 of the top 1 bit outside the address space
Exp resetExp = fromInteger(valueOf(TSub#(SizeOf#(LCapAddress),MW)));

Bit#(MW) resetTop = {2'b01,0};
typedef struct
{
    Exp exp;
    Bit#(MW) topBits;
    Bit#(MW) baseBits;
} Bounds deriving (Bits, Eq, FShow);
instance DefaultValue #(Bounds);
    defaultValue = Bounds {
        exp     : resetExp,
        topBits : resetTop,
        baseBits: 0
    };
endinstance
instance DefaultValue #(CapFat);
    defaultValue = CapFat {
        isCapability: True,
        perms       : unpack(~0),
        reserved    : 0,
        otype       : -1,
        format      : EmbeddedExp,
        bounds      : defaultValue,
        address     : 0,
        addrBits    : 0
    };
endinstance

CapFat nullCap = CapFat {
    isCapability: False,
    perms       : unpack(0),
    reserved    : 0,
    otype       : -1,
    format      : EmbeddedExp,
    bounds      : defaultValue,
    address     : 0,
    addrBits    : 0
};

///////////////////////////////////////////////
// CHERI CONCENTRATE, example 128-bit format //
///////////////////////////////////////////////
// In memory representation //
////////////////////////////////////////////////////////////////////////////////
/*
                    Embedded Exp
127___124_123_112_111_109_108__91__90_89_________________________78_77__________________________64
|        |       |       |       |   |                             |                             |
| uperms | perms |  res  | otype | 0 |                    top<11:0>|                   base<13:0>| Exp0
| uperms | perms |  res  |       | 1 |             top<11:3>|e<5:3>|            base<13:3>|e<2:0>| EmbeddedExp
|________|_______|_______|_______|___|_____________________________|_____________________________|
63_______________________________________________________________________________________________0
|                                                                                                |
|                                      address                                                   |
|________________________________________________________________________________________________|

reconstructing most significant top bits:
top<20:19> = base<20:19> + carry_out + len_correction
     where
             carry_out      = 1 if top<18:0> < base <18:0>
                              0 otherwise
             len_correction = 0 if Exp0
                              1 otherwise
*/

// These three bounds formats help with the decBounds function.
typedef struct {
  Bool              embeddedExp;
  Bit#(TSub#(MW,2)) top;
  Bit#(MW)          base;
} BoundsExp0 deriving(Bits, Eq, FShow);

typedef struct {
  Bool                              embeddedExp;
  Bit#(TSub#(MW,TAdd#(HalfExpW,2))) topUpperBits;
  Bit#(HalfExpW)                    expTopHalf;
  Bit#(TSub#(MW,HalfExpW))          baseUpperBits;
  Bit#(HalfExpW)                    expBotHalf;
} BoundsEmbeddedExp deriving(Bits, Eq, FShow);

function Tuple2#(Format, Bounds) decBounds (CBounds raw);
    Bit#(2) fmt     = truncateLSB(raw);
    Format format   = (fmt[1] == 1'b0) ? Exp0 : EmbeddedExp;
    Bounds bounds   = defaultValue;
    bounds.exp      = 0;
    bounds.topBits  = 0;
    bounds.baseBits = 0;
    case (format)
        EmbeddedExp: begin
            BoundsEmbeddedExp b = unpack(raw);
            bounds.exp          = unpack({b.expTopHalf,b.expBotHalf});
            bounds.topBits      = {2'b00,b.topUpperBits,0};
            bounds.baseBits     = {b.baseUpperBits,0};
        end
        default: begin // and Exp0
          BoundsExp0 b    = unpack(raw);
          bounds.topBits  = {2'b00,b.top};
          bounds.baseBits = b.base;
        end
    endcase
    // topBits = baseBits + lengthBits. lengthBits is not present here, but the MSB of lengthBits can be implied to be 1.
    // To calculate the upper bits of of top, we need the oritinal carry out from the lower bits of base + length, which we find like so:
    Bit#(TSub#(MW,2)) topBits  = truncate(bounds.topBits);
    Bit#(TSub#(MW,2)) baseBits = truncate(bounds.baseBits);
    Bit#(2) carry_out = (topBits < baseBits) ? 2'b01 : 2'b00;
    Bit#(2) len_correction = case (format)
                                  Exp0: 2'b00;
                                  default: 2'b01;
                              endcase;
    Bit#(2) impliedTopBits = truncateLSB(bounds.baseBits) + carry_out + len_correction;
    bounds.topBits = {impliedTopBits,truncate(bounds.topBits)};
    return tuple2(format,bounds);
endfunction

function CBounds encBounds (Format format, Bounds bounds);
    Bit#(HalfExpW)   hiExpBits   = truncateLSB(pack(bounds.exp));
    Bit#(HalfExpW)   loExpBits   = truncate(pack(bounds.exp));

    Bit#(TSub#(MW,TAdd#(HalfExpW,2))) eExpTop = truncate(bounds.topBits >> valueOf(HalfExpW));
    Bit#(TSub#(MW,HalfExpW))         eExpBase = truncateLSB(bounds.baseBits);

    return case (format)
               Exp0: {1'b0, truncate(bounds.topBits), bounds.baseBits};
               EmbeddedExp: {1'b1, eExpTop, hiExpBits, eExpBase, loExpBits};
           endcase;
endfunction

typedef struct {
  Bit#(3)   repBoundTopBits;
  Bool      topHi;
  Bool      baseHi;
  Bool      addrHi;
  Int#(2)   topCorrection;
  Int#(2)   baseCorrection;
} MetaInfo deriving(Bits, FShow);

function MetaInfo getMetaInfo (CapFat cap);
    Bit#(3) tb = truncateLSB(cap.bounds.topBits);
    Bit#(3) bb = truncateLSB(cap.bounds.baseBits);
    Bit#(3) ab = truncateLSB(cap.addrBits);
    Bit#(3) repBound = bb - 3'b001;
    Bool topHi  = tb < repBound;
    Bool baseHi = bb < repBound;
    Bool addrHi = ab < repBound;
    Int#(2) topCorrection  = (topHi  == addrHi) ? 0 : ((topHi  && !addrHi) ? 1 : -1);
    Int#(2) baseCorrection = (baseHi == addrHi) ? 0 : ((baseHi && !addrHi) ? 1 : -1);
    return MetaInfo {
        repBoundTopBits: repBound,
        topHi          : topHi,
        baseHi         : baseHi,
        addrHi         : addrHi,
        topCorrection  : topCorrection,
        baseCorrection : baseCorrection
    };
endfunction
