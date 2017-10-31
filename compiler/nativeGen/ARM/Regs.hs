{-# LANGUAGE CPP #-}

module ARM.Regs (
  -- * Address Modes
  AddrMode(..),
  -- * Immediates
  Imm(..)
) where

#include "nativeGen/NCG.h"
#include "HsVersions.h"

import           GhcPrelude

import           Format
import           Reg              (RealReg (..), regSinlge)
import           RegClass

import           CLabel           (CLabel)
import           Cmm
import           Unique

import           CodeGen.Platform
import           DynFlags
import           Outputable
import           Platform

import           Data.Int         (Int16, Int32, Int64, Int8)
import           Data.Word        (Word16, Word32, Word64, Word8)

data Address
  = ZeroOffset            Rn
  | PreIndexedRegister    Rn RegOffset
  | PreIndexedImmediate   Rn ImmOffset
  | PostIndexedRegister   Rn RegOffset
  | PostIndexedImmediate  Rn ImmOffset

data Imm
  = ImmNumericConstant Word32

data RegOffset
  = PlusReg Reg
  | MinusReg Reg

data ImmOffset
  = PlusImm Imm
  | MinusImm Imm

-- ARM has sixteen registers visible at any one time.
-- They are named R0 to R15. All are 32 bits wide.
r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15 :: Reg
r0      = regSingle 0
r1      = regSingle 1
r2      = regSingle 2
r3      = regSingle 3
r4      = regSingle 4
r5      = regSingle 5
r6      = regSingle 6
r7      = regSingle 7
r8      = regSingle 8
r9      = regSingle 9
r10     = regSingle 10
r11     = regSingle 11
r12     = regSingle 12
r13     = regSingle 13
r14     = regSingle 14
r15     = regSingle 15

-- R13 is also known as SP (stack pointer).
sp     :: Reg
sp      = r13

-- R14 is also known as LR (link register which holds caller's return address).
lr     :: Reg
lr      = r14

-- R15 is also known as PC (program counter).
pc     :: Reg
pc      = r15

-- CPSR (current program status register) is an additional
-- special register that holds flags like overflow
-- of logical an arithmetic operations.
cpsr   :: Reg
cpsr    = regSingle 9999 -- doesn't have a number in specification

litToImm :: CmmLit -> Imm
litToImm (CmmInt i w) = ImmInteger (narrowS w i)
litToImm _            = panic "ARM.Regs.litToImm: no match"
