{-# LANGUAGE CPP   #-}
{-# LANGUAGE GADTs #-}
module ARM.CodeGen (
  cmmTopCodeGen,
  generateJumpTableForInstr,
  InstrBlock
) where

#include "HsVersions.h"
#include "nativeGen/NCG.h"
#include "../includes/MachDeps.h"

-- NCG stuff:
import           GhcPrelude

import           CodeGen.Platform
import           CPrim
import           Format
import           Instruction
import           NCGMonad
import           PIC
import           Platform
import           PPC.Cond
import           PPC.Instr
import           PPC.Regs
import           Reg
import           RegClass
import           TargetReg

-- Our intermediate code:
import           BlockId
import           CLabel
import           Cmm
import           CmmSwitch
import           CmmUtils
import           Hoopl.Block
import           Hoopl.Graph
import           PprCmm           (pprExpr)

-- The rest:
import           DynFlags
import           OrdList
import           Outputable

import           Control.Monad    (mapAndUnzipM, when)
import           Data.Bits
import           Data.Word

import           BasicTypes
import           FastString
import           Util

-- | Memory addressing modes passed up the tree.
data Amode
  = Amode AddrMode InstrBlock

-- | Register's passed up the tree.
--
--   If the stix code forces the register
--   to live in a pre-decided machine register, it comes out as @Fixed@;
--   otherwise, it comes out as @Any@, and the parent can decide which
--   register to put it in.
data Register
  = Fixed Format Reg InstrBlock
  | Any   Format (Reg -> InstrBlock)

-- | Make code to evaluate a 32 bit expression.
getRegister :: CmmExpr -> NatM Register
getRegister expr = case expr of
  -- A literal gets loaded via numeric
  -- constant expression (i.e. `LDR rd, =0x123`).
  -- The arm assembler decides based on size whether
  -- it can be done via MOV or requires an LDR and
  -- an entry in the lit pool.
  CmmLit lit -> do
    let code dst = unitOL $ LDR' dst (litToImm lit)
    return $ Any format code
  -- Compute an inner expression representing
  -- a memory address and then load from this address.
  -- The code for the computation of the inner
  -- address is prepended to the load instruction.
  CmmLoad mem pk -> do
    Amode addr code <- getAmode mem
    let format = cmmTypeFormat pk
    let code' dst = code `snocOL` LDR AL dst addr
    return $ Any format code'
  -- Map and return the given register.
  -- TODO: This is the easiest implementation taken from SPARC.
  --       Is this correct? Other arches handle PicBaseReg etc.
  CmmReg reg -> do
    dflags <- getDynFlags
    let platform = targetPlatform dflags
    return $ Fixed (cmmTypeFormat $ cmmRegType dflags reg)
                   (getRegisterReg platform reg) nilOL
  -- TODO: How does it work?
  CmmRegOff {} -> do
    dflags <- getDynFlags
    getRegister (mangleIndexTree dflags expr)
  --
  CmmMachOp op exprs ->
    getRegisterForMachOp op exprs
  -- This one is not implemented (at least in PPC).
  -- TODO: What shall be done here?
  CmmStackSlot {} ->
    panic "ARM.CodeGen.getRegister: CmmStackSlot not implemented"
  where
    -- | Get the corresponding machine register for a cmm register.
    --   Local registers are mapped to virtual registers.
    --   Global register mapping is defined in `includes/CodeGen.Platform.hs`.
    getRegisterReg :: Platform -> CmmReg -> Reg
    getRegisterReg _ (CmmLocal (LocalReg u pk)) =
      RegVirtual $ mkVirtualReg u (cmmTypeFormat pk)
    getRegisterReg platform (CmmGlobal mid) =
      case globalRegMaybe platform mid of
        Just reg -> RegReal reg
        Nothing  -> panic "ARM.CodeGen.getRegisterReg: global is in memory"
    -- TODO: What does it do?
    mangleIndexTree :: DynFlags -> CmmExpr -> CmmExpr
    mangleIndexTree dflags (CmmRegOff reg off) =
      CmmMachOp (MO_Add width)
                [CmmReg reg, CmmLit (CmmInt (fromIntegral off) width)]
      where
        width = typeWidth (cmmRegType dflags reg)

getRegisterMachOp :: MachOp -> [CmmExpr] -> NatM Register
getRegisterMachOp op params = case op of
  -----------------------------------------------------------------------------
  -- Integer operations (insensitive to signed/unsigned).
  -----------------------------------------------------------------------------

  MO_Add w -> binary w $ \rd rn rm->
    [ ADD AL rd rn (Op2 rm) ]

  MO_Sub w -> binary w $ \rd rn rm->
    [ SUB AL rd rn (Op2 rm) ]

  MO_Mul w -> binary w $ \rd rn rm->
    [ MUL AL rd rn (Op2 rm) ]

  MO_Eq  w -> binary w $ \rd rn rm->
    [ TEQ rn rm, LDR' EQ rd (ImmInt 1) ]

  MO_Ne  w -> binary w $ \rd rn rm->
    [ TEQ rn rm, LDR' EQ rd (ImmInt 1) ]

  -----------------------------------------------------------------------------
  -- Bitwise operations.  Not all of these may be supported
  -- at all sizes, and only integral ws are valid.
  -----------------------------------------------------------------------------

  MO_And   w -> binary w $ \rd rn rm->
    [ AND AL rd rn (Op2 rm) ]

  MO_Or    w -> binary w $ \rd rn rm->
    [ OR AL rd rn (Op2 rm) ]

  MO_Xor   w -> binary w $ \rd rn rm->
    [ EOR AL rd rn (Op2 rm) ]

  MO_Not   w -> unary w $ \rd rn->
    [ NEG AL rd rn ]

  MO_Shl   w -> binary w $ \rd rn rm->
    [ AND AL rd rn (Op2 rm) ]

  MO_U_Shr w -> binary w $ \rd rn rm->
    [ AND AL rd rn (Op2 rm) ]

  MO_S_Shr w -> binary w $ \rd rn rm->
    [ AND AL rd rn (Op2 rm) ]

  -----------------------------------------------------------------------------
  -- Signed multiply/divide.
  -----------------------------------------------------------------------------

  MO_S_MulMayOflo w -> binary w $ \rd rn rm->
    [ MUL AL rd rn (Op2 rm) ]

  -- FIXME: What about div by zero?
  MO_S_Quot w -> binary w $ \rd rn rm->
    [ SDIV AL rd rn (Op2 rm) ]

  MO_S_Rem w -> binary w $ \rd rn rm->
    [ SDIV AL rd rn (Op2 rm)   -- rd := rn / rm
    , MUL  AL rd rm (Op2 rd)   -- rd := rm * rd
    , SUB  AL rd rn (Op2 rd) ] -- rd := rn - rd

  -----------------------------------------------------------------------------
  -- Signed negate.
  -----------------------------------------------------------------------------

  MO_S_Neg w -> unary w $ \rd rn->
    [ NEG  AL rd rn
    , ADD  AL rd rd (Op2' $ ImmInt 1) ]

  -----------------------------------------------------------------------------
  -- Unsigned multiply/divide.
  -----------------------------------------------------------------------------

  MO_U_MulMayOflo w -> binary w $ \rd rn rm->
    [ MUL AL rd rn (Op2 rm) ]

  MO_U_Quot w -> binary w $ \rd rn rm->
    [ SDIV AL rd rn (Op2 rm) ]

  MO_U_Rem w -> binary w $ \rd rn rm->
    [ SDIV AL rd rn (Op2 rm)   -- rd := rn / rm
    , MUL  AL rd rm (Op2 rd)   -- rd := rm * rd
    , SUB  AL rd rn (Op2 rd) ] -- rd := rn - rd

  -----------------------------------------------------------------------------
  -- Signed comparisons.
  -----------------------------------------------------------------------------

  MO_S_Ge w -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' GE rd (ImmInt 1) ]

  MO_S_Le w -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' LE rd (ImmInt 1) ]

  MO_S_Gt w -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' GT rd (ImmInt 1) ]

  MO_S_Lt w -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' LT rd (ImmInt 1) ]

  -----------------------------------------------------------------------------
  -- Unsigned comparisons.
  -----------------------------------------------------------------------------

  MO_U_Ge w -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' CS rd (ImmInt 1) ]

  MO_U_Le w -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' LS rd (ImmInt 1) ]

  MO_U_Gt w  -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' HI rd (ImmInt 1) ]

  MO_U_Lt w -> binary w $ \rd rn rm->
    [ CMP  AL rn (Op2 rm)
    , LDR' CC rd (ImmInt 1) ]

  -----------------------------------------------------------------------------
  -- Floating point arithmetic.
  -----------------------------------------------------------------------------

  MO_F_Add  w -> binary w $ \fd fn fm->
    [ VADD AL F32 fd fn fm ]

  MO_F_Sub  w -> binary w $ \fd fn fm->
    [ VSUB AL F32 fd fn fm ]

  MO_F_Mul  w -> binary w $ \fd fn fm->
    [ VMUL AL F32 fd fn fm ]

  MO_F_Quot w -> binary w $ \fd fn fm->
    [ VDIV AL F32 fd fn fm ]

  MO_F_Neg  w -> unary w $ \fd fm->
    [ VNEG AL F32 fd fm ]

  -----------------------------------------------------------------------------
  -- Floating point comparison.
  -----------------------------------------------------------------------------

  MO_F_Eq w -> binary w $ \rd fn fm->
    [ VCMP AL F32 fn fm
    , LDR' EQ rd (ImmInt 1) ]

  MO_F_Ne w -> binary w $ \rd fn fm->
    [ VCMP AL F32 fn fm
    , LDR' NE rd (ImmInt 1) ]

  MO_F_Ge w -> binary w $ \rd fn fm->
    [ VCMP AL F32 fn fm
    , LDR' GE rd (ImmInt 1) ]

  MO_F_Le w -> binary w $ \rd fn fm->
    [ VCMP AL F32 fn fm
    , LDR' LE rd (ImmInt 1) ]

  MO_F_Gt w -> binary w $ \rd fn fm->
    [ VCMP AL F32 fn fm
    , LDR' GT rd (ImmInt 1) ]

  MO_F_Lt w -> binary w $ \rd fn fm->
    [ VCMP AL F32 fn fm
    , LDR' LT rd (ImmInt 1) ]

  -----------------------------------------------------------------------------
  -- Conversions.  Some of these will be NOPs.
  -- Floating-point conversions use the signed variant.
  -----------------------------------------------------------------------------

  MO_SF_Conv w w         -> undefined
  MO_FS_Conv w w         -> undefined
  MO_SS_Conv w w         -> undefined
  MO_UU_Conv w w         -> undefined
  MO_FF_Conv w w         -> undefined

  -- Vector element insertion and extraction operations
  MO_V_Insert  Length w  -> undefined
  MO_V_Extract Length w  -> undefined

  -- Integer vector operations
  MO_V_Add Length w      -> undefined
  MO_V_Sub Length w      -> undefined
  MO_V_Mul Length w      -> undefined

  -- Signed vector multiply/divide
  MO_VS_Quot Length w    -> undefined
  MO_VS_Rem  Length w    -> undefined
  MO_VS_Neg  Length w    -> undefined

  -- Unsigned vector multiply/divide
  MO_VU_Quot Length w    -> undefined
  MO_VU_Rem  Length w    -> undefined

  -- Floting point vector element insertion and extraction operations
  MO_VF_Insert  Length w -> undefined
  MO_VF_Extract Length w -> undefined

  -- Floating point vector operations
  MO_VF_Add  Length w    -> undefined
  MO_VF_Sub  Length w    -> undefined
  MO_VF_Neg  Length w    -> undefined
  MO_VF_Mul  Length w    -> undefined
  MO_VF_Quot Length w    -> undefined

  -- Alignment check (for -falignment-sanitisation)
  MO_AlignmentCheck i w  -> undefined
  where
    unary w f = case params of
        [x] -> do
          (rn, cn) <- getSomeReg x
          return $ Any (intFormat w) (\rd-> cn <> toOL (f rd rn))
        _ -> panic "ARM.CodeGen.getRegisterMachOp.unary: parameter mismatch"
    binary w f = case params of
      [x,y] -> do
        (rn, cn) <- getSomeReg x
        (rm, cm) <- getSomeReg y
        return $ Any (intFormat w) (\rd-> cn <> cm <> toOL (f rd rn rm))
      _ -> panic "ARM.CodeGen.getRegisterMachOp.binary: parameter mismatch"

-- | Compute an expression into a register, but
--   we don't mind which one it is.
getSomeReg :: CmmExpr -> NatM (Reg, InstrBlock)
getSomeReg expr = do
  r <- getRegister expr
  case r of
    Any rep code -> do
        tmp <- getNewRegNat rep
        return (tmp, code tmp)
    Fixed _ reg code ->
        return (reg, code)

-- | Generate an unconditional jump.
genJump :: CmmExpr -> [Reg] -> NatM InstrBlock
genJump expr regs = case expr of
  -- Jump directly to the immediate address.
  -- Use MOV to set program counter.
  CmmLit lit ->
     return $ unitOL $ MOV AL pc $ Op2' $ litToImm lit
  --
  CmmLoad mem _ -> do
    Amode target code <- getAmode mem
    return (code `snocOL` JMP (OpAddr target) regs)

  _ -> do
    (reg,code) <- getSomeReg expr
    return (code `snocOL` JMP (OpReg reg) regs)
