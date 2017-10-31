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
  = Fixed Reg InstrBlock
  | Any   (Reg -> InstrBlock)

-- | Make code to evaluate a 32 bit expression.
getRegister :: CmmExpr -> NatM Register
getRegister expr = case expr of
  -- A literal gets loaded via numeric
  -- constant expression (i.e. `LDR rd, =0x123`).
  -- The arm assembler decides based on size whether
  -- it can be done via MOV or requires an LDR and
  -- entry in the lit pool.
  CmmLit lit ->
    return $ Any $ \dst-> unitOL $ LDR' dst (litToImm lit)
  --
  CmmReg reg -> case reg of
    CmmLocal (LocalReg uniq cmmType) ->
      undefined
    CmmGlobal _ ->
      undefined

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
