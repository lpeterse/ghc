{-# LANGUAGE CPP #-}

#include "HsVersions.h"
#include "nativeGen/NCG.h"

module ARM.Instr (
  RI(..),
  Instr(..)
) where

import           GhcPrelude

import           Format
import           Instruction
import           PPC.Cond
import           PPC.Regs
import           Reg
import           RegClass
import           TargetReg

import           BlockId
import           CLabel
import           Cmm
import           CmmInfo
import           CodeGen.Platform
import           DynFlags
import           FastString
import           Hoopl.Collections
import           Hoopl.Label
import           Outputable
import           Platform
import           UniqFM            (listToUFM, lookupUFM)
import           UniqSupply

import           Control.Monad     (replicateM)
import           Data.Maybe        (fromMaybe)

instance Instruction Instr where
  regUsageOfInstr         = arm_regUsageOfInstr
  patchRegsOfInstr        = arm_patchRegsOfInstr
  isJumpishInstr          = arm_isJumpishInstr
  jumpDestsOfInstr        = arm_jumpDestsOfInstr
  patchJumpInstr          = arm_patchJumpInstr
  mkSpillInstr            = arm_mkSpillInstr
  mkLoadInstr             = arm_mkLoadInstr
  takeDeltaInstr          = arm_takeDeltaInstr
  isMetaInstr             = arm_isMetaInstr
  mkRegRegMoveInstr _     = arm_mkRegRegMoveInstr
  takeRegRegMoveInstr     = arm_takeRegRegMoveInstr
  mkJumpInstr             = arm_mkJumpInstr
  mkStackAllocInstr       = arm_mkStackAllocInstr
  mkStackDeallocInstr     = arm_mkStackDeallocInstr

data Cond
  = EQ -- Equal
  | NE -- Not equal
  | CS -- Carry Set / Unsigned higher or same
  | CC -- Carry Set / Unsigned higher or same
  | MI -- Negative
  | PL -- Positive or zero
  | VS -- Overflow
  | VC -- Overflow
  | HI -- Unsigned higher
  | LS -- Unsigned lower or same
  | GE -- Signed greater than or equal
  | LT -- Signed less than
  | GT -- Signed greater than
  | LE -- Signed less than or equal
  | AL -- Always
  deriving Eq

data Size
  = B   -- byte
  | SB  -- byte (signed)
  | H   -- half word
  | SH  -- half-word (signed)
  deriving Eq

-- Register or immediate.
data RI     = RIReg Reg | RIImm Imm
type Offset = RI

data Op2
  = Op2     Reg
  | Op2'    Imm
  | Op2LSL  Reg Reg
  | Op2LSL' Reg Imm
  | Op2LSR  Reg Reg
  | Op2LSR' Reg Imm
  | Op2ASR  Reg Reg
  | Op2ASR' Reg Imm
  | Op2ROR  Reg Reg
  | Op2ROR' Reg Imm

type Rd     = Reg
type Rn     = Reg
type Rm     = Reg
type Rs     = Reg

data Instr
  -- Comment pseudo-op.
  = COMMENT  FastString
  -- Some static data spat out during code
  -- generation.  Will be extracted before
  -- pretty-printing.
  | LDATA    Section CmmStatics
  -- Start a new basic block.  Useful during
  -- codegen, removed later.  Preceding
  -- instruction should be a jump, as per the
  -- invariants for a BasicBlock (see Cmm).
  | NEWBLOCK BlockId
  -- Specify current stack offset for
  -- benefit of subsequent passes.
  | DELTA    Int
  -- Loads and stores.
  | LDR  Cond Rd Address
  | LDRB Cond Rd Address
  | STR  Cond Rd Address
  | STRB Cond Rd Address
  -- Arithmetic operations.
  | ADD  Rd Rn Op2            -- Rd := Rn + Op2
  | ADC  Rd Rn Op2            -- Rd := Rn + Op2 + Carry
  | SUB  Rd Rn Op2            -- Rd := Rn – Op2
  | SBC  Rd Rn Op2            -- Rd := Rn – Op2 – NOT(Carry)
  | MUL  Rd Rm Rs             -- Rd := (Rm * Rs)[31:0]
  | SDIV Rd Rn Rm             -- Rd := Rn / Rm
  | UDIV Rd Rn Rm             -- Rd := Rn / Rm
  -- Moves operations.
  | MOV  Rd    Op2            -- Rd := Op2
  | MOVS Rd    Op2            -- Rd := Op2
  | MVN  Rd    Op2            -- Rd := 0xFFFFFFFF EOR Op2
  | MVNS Rd    Op2            -- Rd := 0xFFFFFFFF EOR Op2
  -- Compare operations.
  | CMP     Rn Op2            -- Update CPSR flags on Rn – Op2
  | CMN     Rn Op2            -- Update CPSR flags on Rn + Op2
  -- Logical operations.
  | TST     Rn Op2            -- Update CPSR flags on Rn AND Op2
  | TEQ     Rn Op2            -- Update CPSR flags on Rn EOR Op2
  | AND  Rd Rn Op2            -- Rd := Rn AND Op2
  | EOR  Rd Rn Op2            -- Rd := Rn EOR Op2
  | ORR  Rd Rn Op2            -- Rd := Rn ORR Op2
  | ORN  Rd Rn Op2            -- Rd := Rn ORN Op2
  | BIC  Rd Rn Op2            -- Rd := Rn AND NOT Op2
  -- Swap instruction.
  | SWP  Cond Rd Rm Rn        -- temp := [Rn], [Rn] := Rm, Rd := temp
  | SWPB Cond Rd Rm Rn        -- temp := ZeroExtend([Rn][7:0]), [Rn][7:0] := Rm[7:0], Rd := temp
  -- Software interrupt instruction.
  | SWI  Cond Imm
